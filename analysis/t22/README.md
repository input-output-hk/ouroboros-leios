# lean-leios

A minimal Lean 4 model of Linear Leios for analysing T22 of the threat model: an adversary
lets an EB get certified while withholding it from most honest nodes, so that the certificate
RB cannot be selected in time.

## Model and assumptions

- Times are slot numbers; "by slot `t`" means `recv ≤ t`. The Praos paper uses strict
  inequalities (`i + Δ < j`), so boundaries shift by one slot when mapping between the two.
- `Δ` is the Praos `Δ`-semi-synchrony bound, applied to RBs only. `D` is the same kind of bound
  applied to EBs and is kept separate because EBs are several times larger than RBs; the
  theorems state by how much `D` may exceed `Δ`, namely by `Ldiff`.
- "Holding" an EB means its closure is fetched and validated against the announcing RB's state,
  for a voter and for a node selecting the certificate RB alike. The CIP budgets this
  reapplication separately from diffusion; here it is folded into `D`, so a measured diffusion
  time needs the validation time added.
- Verifying the certificate and applying the certificate RB is per-RB work assumed to fit in
  `Δ` like any RB. This is a composition assumption, not something proved here.
- The quorum `τ` is assumed at least one half (`Params.τ_ge_half`); with an honest majority this
  makes a certificate evidence of at least one honest vote.
- Two voting rules are modelled through `voteRecvOffset`: the prototype votes if the EB is held
  by the vote deadline (`3·Lhdr + Lvote`), the Agda/CIP specification requires it within `Lhdr`.
- The theorems in `Leios/T22.lean` take the offset as a parameter. Their condition
  `voteRecvOffset + D ≤ certGap + Δ` reduces under the prototype rule to `D ≤ Ldiff + Δ`
  (`12 ≤ 7 + 5` with the glossary values); `t22_cannot_happen` shows the attack fails under it
  and `t22_can_happen` builds a witness when it fails.

## Build

```sh
nix develop
lake exe cache get   # Mathlib oleans
lake build --wfail
```

## Map

| file                 | contents                                              |
|----------------------|-------------------------------------------------------|
| `Leios/Params.lean`  | protocol and environment parameters                   |
| `Leios/Model.lean`   | one pipeline: parties, stake, votes, diffusion, harm  |
| `Leios/T22.lean`     | T22 cannot happen iff `L_diff` is sized for `D`        |
| `Leios/Prob.lean`    | probability bound when `L_diff` is `k` slots too small |
