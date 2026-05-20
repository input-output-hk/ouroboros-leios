//! Outbound transform — per-peer rewriting of about-to-send artefacts.
//!
//! [`Behaviour::transform_outbound`] is called by the I/O wrapper
//! before each peer-targeted send.  A behaviour can
//! [`Send`](OutboundDecision::Send) the artefact unchanged,
//! [`Drop`](OutboundDecision::Drop) it (suppress delivery to this
//! peer), [`Replace`](OutboundDecision::Replace) it with a different
//! artefact (peer-split equivocation, eclipse fake tips), or
//! [`Augment`](OutboundDecision::Augment) with extras.
//!
//! The variant set is narrow on purpose — extend as new use cases
//! need new wire artefacts.  Adding a variant: append to both
//! [`Outbound`] (borrowed view passed in) and [`OwnedOutbound`]
//! (owned, returned by `Replace`/`Augment`).
//!
//! [`Behaviour::transform_outbound`]: super::Behaviour::transform_outbound

/// Borrowed view of an outbound artefact passed to
/// [`Behaviour::transform_outbound`].  Carries the minimum logical
/// metadata a behaviour needs to recognise the artefact (e.g. its
/// slot) plus the opaque wire bytes — CBOR decoding stays in the I/O
/// wrapper.
///
/// [`Behaviour::transform_outbound`]: super::Behaviour::transform_outbound
#[derive(Debug, Clone, Copy)]
pub enum Outbound<'a> {
    /// RB header about to be advertised to a peer.  `slot` is the
    /// header's block-slot — useful for recognising self-produced
    /// equivocation slots.
    RbHeader { slot: u64, header: &'a [u8] },
}

/// Owned counterpart of [`Outbound`], returned by `Replace` / `Augment`.
#[derive(Debug, Clone)]
pub enum OwnedOutbound {
    RbHeader { slot: u64, header: Vec<u8> },
}

/// What the behaviour decided for this peer-targeted send.
#[derive(Debug, Clone, Default)]
pub enum OutboundDecision {
    /// Send the artefact unchanged.  The default.
    #[default]
    Send,
    /// Suppress delivery — the wire path emits nothing for this peer.
    Drop,
    /// Replace the artefact with a different one.  Used by
    /// equivocation (different RB variant per peer subset) and
    /// eclipse (fake tip injected for the target peer).
    Replace(OwnedOutbound),
    /// Send the original artefact AND these extras.
    Augment(Vec<OwnedOutbound>),
}

impl OutboundDecision {
    pub fn is_send(&self) -> bool {
        matches!(self, OutboundDecision::Send)
    }
}
