# Changelog

# Unreleased

## Linear Leios
- Allow RBs to include EB certificates produced at least `L_diff` slots ago, instead of `L_vote + L_diff` slots ago. When `L_diff` is 0, this removes any direct time factor from the decision to include an EB cert.
- Add TXs to the mempool, even if they belong to an EB we've already seen.

# v0.1.0

This version was arbitrarily chosen as the point to start tracking major changes to the simulation. 