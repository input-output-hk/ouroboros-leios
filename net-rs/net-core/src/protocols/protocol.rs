//! Mini-protocol state machine framework.
//!
//! Each Ouroboros mini-protocol is a state machine where exactly one side
//! (client or server) has "agency" — the right to send the next message —
//! in each state. This module provides the traits and runner for defining
//! and running protocols over the CBOR codec.
//!
//! # Design
//!
//! The `Protocol` trait defines the state machine (states, messages,
//! transitions, limits). The `Runner` wraps a codec pair and tracks
//! state, providing `send()` and `recv()` methods that enforce agency
//! and advance the state machine. Protocol implementations use the
//! Runner directly in their async client/server functions.

use std::fmt::Debug;
use std::time::Duration;

use crate::mux::MuxError;
use crate::mux::{CodecRecv, CodecSend};

/// Which side has the right to send in a given state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Agency {
    /// The client (initiator / downstream peer) must send.
    Client,
    /// The server (responder / upstream peer) must send.
    Server,
    /// Neither side sends — the protocol has terminated.
    Nobody,
}

/// The local role in a protocol exchange.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Client,
    Server,
}

/// Defines a mini-protocol's state machine: states, messages, transitions,
/// and per-state limits.
pub trait Protocol: Send + 'static {
    /// The state type. Must be cheaply cloneable for transition checks.
    type State: Clone + Debug + Send;

    /// The message type. All variants in one enum, tagged by CBOR array index.
    type Message: for<'a> minicbor::Decode<'a, ()> + minicbor::Encode<()> + Debug + Send;

    /// The initial state when the protocol starts.
    fn initial_state() -> Self::State;

    /// Which side has agency in the given state.
    fn agency(state: &Self::State) -> Agency;

    /// Compute the next state after a message. Returns an error if the
    /// message is invalid for the current state.
    fn transition(state: &Self::State, msg: &Self::Message) -> Result<Self::State, ProtocolError>;

    /// Maximum message size (bytes) allowed in the given state.
    /// Must be nonzero — Runner will panic if this returns 0, and
    /// the demuxer will reject all data for a protocol with limit 0.
    fn size_limit(state: &Self::State) -> usize;

    /// Timeout for receiving a message in the given state.
    /// `None` means no timeout (wait forever).
    fn timeout(_state: &Self::State) -> Option<Duration> {
        None
    }
}

/// Errors from protocol operation.
#[derive(Debug, thiserror::Error)]
pub enum ProtocolError {
    #[error("agency violation: we are {role:?} but {agency:?} has agency")]
    AgencyViolation { role: Role, agency: Agency },

    #[error("invalid message for current state: {0}")]
    InvalidMessage(String),

    #[error("protocol timeout after {0:?}")]
    Timeout(Duration),

    #[error("message too large: {size} bytes exceeds limit {limit}")]
    MessageTooLarge { size: usize, limit: usize },

    #[error("protocol terminated (state has Nobody agency)")]
    Terminated,

    #[error("mux error: {0}")]
    Mux(#[from] MuxError),
}

/// Runs a protocol over a codec, tracking state and enforcing agency.
///
/// Protocol implementations use this to build their client/server logic:
/// ```ignore
/// let mut runner = Runner::<Handshake>::new(Role::Client, send, recv);
/// runner.send(&MsgProposeVersions { ... }).await?;
/// let response = runner.recv().await?;
/// ```
pub struct Runner<P: Protocol> {
    role: Role,
    state: P::State,
    codec_send: CodecSend,
    codec_recv: CodecRecv,
}

impl<P: Protocol> Runner<P> {
    /// Create a new runner starting in the protocol's initial state.
    ///
    /// # Panics
    ///
    /// Panics if `P::size_limit()` returns 0 for the initial state. Every
    /// protocol must define a nonzero size limit for all states.
    pub fn new(role: Role, codec_send: CodecSend, codec_recv: CodecRecv) -> Self {
        let initial_state = P::initial_state();
        let limit = P::size_limit(&initial_state);
        assert!(
            limit > 0,
            "protocol size_limit must be nonzero for all states"
        );
        codec_recv.set_ingress_limit(limit);

        Self {
            role,
            state: initial_state,
            codec_send,
            codec_recv,
        }
    }

    /// The current protocol state.
    pub fn state(&self) -> &P::State {
        &self.state
    }

    /// Whether the local side currently has agency.
    pub fn has_agency(&self) -> bool {
        matches!(
            (P::agency(&self.state), self.role),
            (Agency::Client, Role::Client) | (Agency::Server, Role::Server)
        )
    }

    /// Whether the protocol has terminated.
    pub fn is_done(&self) -> bool {
        P::agency(&self.state) == Agency::Nobody
    }

    /// Send a message. Checks that we have agency and the message is valid
    /// for the current state, then encodes and sends it, advancing the state.
    pub async fn send(&mut self, msg: &P::Message) -> Result<(), ProtocolError> {
        let agency = P::agency(&self.state);
        if agency == Agency::Nobody {
            return Err(ProtocolError::Terminated);
        }

        // Check that we have agency.
        let we_have_agency = matches!(
            (agency, self.role),
            (Agency::Client, Role::Client) | (Agency::Server, Role::Server)
        );
        if !we_have_agency {
            return Err(ProtocolError::AgencyViolation {
                role: self.role,
                agency,
            });
        }

        // Validate the transition.
        let next_state = P::transition(&self.state, msg)?;

        // Send.
        self.codec_send.send(msg).await?;

        self.state = next_state;

        // Update the demuxer's ingress limit for the new state. After
        // sending, the remote side typically has agency and will respond,
        // so set the limit before data arrives.
        self.codec_recv
            .set_ingress_limit(P::size_limit(&self.state));

        Ok(())
    }

    /// Receive a message. Checks that the remote side has agency, then
    /// reads and decodes a message, validates the transition, and advances
    /// the state. Returns the received message.
    pub async fn recv(&mut self) -> Result<P::Message, ProtocolError> {
        let agency = P::agency(&self.state);
        if agency == Agency::Nobody {
            return Err(ProtocolError::Terminated);
        }

        // Check that they have agency.
        let they_have_agency = matches!(
            (agency, self.role),
            (Agency::Client, Role::Server) | (Agency::Server, Role::Client)
        );
        if !they_have_agency {
            return Err(ProtocolError::AgencyViolation {
                role: self.role,
                agency,
            });
        }

        // Set the demuxer's ingress limit for the current state, so
        // oversized data is rejected at the segment level (closest to TCP).
        self.codec_recv
            .set_ingress_limit(P::size_limit(&self.state));

        // Receive with optional timeout.
        let msg: P::Message = match P::timeout(&self.state) {
            Some(duration) => match tokio::time::timeout(duration, self.codec_recv.recv()).await {
                Ok(result) => result?,
                Err(_) => return Err(ProtocolError::Timeout(duration)),
            },
            None => self.codec_recv.recv().await?,
        };

        // Validate the transition.
        let next_state = P::transition(&self.state, &msg)?;

        self.state = next_state;
        Ok(msg)
    }
}
