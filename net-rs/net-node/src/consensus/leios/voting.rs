//! EB-triggered vote production with committee selection.
//!
//! When an EB's election enters the Voting phase, this module decides
//! whether the local node should vote (via CommitteeSelection) and, if
//! so, builds and injects the vote into the network.
//!
//! Planned for Commit 3 of the leios-consensus roadmap.
