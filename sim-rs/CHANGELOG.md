# Changelog

## Unreleased

### Linear Leios

- Respect timings according to the latest CIP draft:
	- RB headers must be received within `Delta_header`
	- Voting must wait until `3 * Delta_header`
	- Voting must finish by `3 * Delta_header + L_vote`
	- EB cannot be referenced until after `3 * Delta_header + L_vote + L_diff`
- Don't include transactions directly in an RB if it also includes an endorsement
- Don't produce empty EBs

### Other

- Fix linter warnings from newer rust version

## v1.2.0

### All Leios variants

Add a `tx-validation-cpu-time-ms-per-byte` setting, a CPU cost which applies to transactions before adding them to the mempool (or to an EB in Linear Leios).

### Linear Leios

Respect cerificate CPU time settings:
 - `cert-generation-cpu-time-ms-constant`
 - `cert-generation-cpu-time-ms-per-node` (currently set to 0)
 - `cert-validation-cpu-time-ms-constant`
 - `cert-validation-cpu-time-ms-per-node` (currently set to 0)

## v1.1.0

### Linear Leios

- Update dependencies to fix vulnerability
- Apply RB/EB validation CPU time when generating new RB/EBs.
- Only vote for EBs if their RB was received within `Δ_header` of its production.

## v1.0.0

### Linear Leios

- Allow RBs to include EB certificates produced at least `L_diff` slots ago, instead of `L_vote + L_diff` slots ago. When `L_diff` is 0, this removes any direct time factor from the decision to include an EB cert.
- Add TXs to the mempool, even if they belong to an EB we've already seen.
- Support choosing attackers by selecting a fraction of stake

### Other

- Add version number to the CLI tool's output.

## v0.1.0

This version was arbitrarily chosen as the point to start tracking major changes to the simulation. 