//! Protocol-level configuration types shared between sim-rs and net-rs.
//!
//! These describe the committee-selection policy and the per-pool stake
//! registry that drive Leios voting. They are protocol parameters, not
//! transport or runtime knobs, so they live with the consensus logic.

use serde::{Deserialize, Serialize};

/// Committee selection mechanism for Leios voting.
///
/// Determines which nodes vote and what type of vote they produce.
#[derive(Debug, Clone, Deserialize, Serialize)]
#[serde(tag = "type")]
pub enum CommitteeSelection {
    /// CIP-0164 spec: weighted Fait Accompli persistent committee (wFA) +
    /// Local Sortition non-persistent voters (LS).
    ///
    /// Per-epoch wFA allocates `persistent_voters` seats deterministically
    /// across pools by stake-weighted lottery (same seed everywhere → same
    /// committee). Each EB also runs a per-pool NPV lottery: each pool
    /// runs `non_persistent_voters` Bernoulli trials at p = stake/total,
    /// and contributes one NPV vote whose eligibility proof carries the
    /// number of wins.
    WfaLs {
        #[serde(default = "default_persistent_voters")]
        persistent_voters: u32,
        #[serde(default = "default_non_persistent_voters")]
        non_persistent_voters: u32,
    },

    /// Each pool with stake casts one vote with weight 1.
    /// Used for testing without sortition / committee allocation.
    EveryoneVotes,

    /// Pools whose cumulative stake (sorted descending) covers the top
    /// `top_centile_of_stake` of total stake each cast one vote with
    /// weight 1.
    StakeCentile {
        #[serde(default = "default_top_centile")]
        top_centile_of_stake: f64,
    },
}

fn default_persistent_voters() -> u32 {
    480
}

fn default_non_persistent_voters() -> u32 {
    120
}

fn default_top_centile() -> f64 {
    0.95
}

impl Default for CommitteeSelection {
    fn default() -> Self {
        CommitteeSelection::WfaLs {
            persistent_voters: default_persistent_voters(),
            non_persistent_voters: default_non_persistent_voters(),
        }
    }
}

impl CommitteeSelection {
    /// Number of NPV trials this node should run per EB. Only WfaLs has
    /// non-persistent voters; the simpler modes return 0.
    pub fn non_persistent_voters(&self) -> u32 {
        match self {
            CommitteeSelection::WfaLs {
                non_persistent_voters,
                ..
            } => *non_persistent_voters,
            _ => 0,
        }
    }
}

/// One entry in the network-wide stake registry. The pair is what each
/// node uses to make ranked-stake committee decisions (top-N, persistent
/// committee), independently arriving at the same answer everywhere.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct StakeEntry {
    pub node_id: String,
    pub stake: u64,
}
