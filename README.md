# ns-lean

Lean 4 / Mathlib library for numerical semigroups — the S.-T. Yau High School Science Award project *Numerical Semigroups, Formalized*.

Write-up, GAP cross-checks, and the literature audit table live in the companion repo: [ns-project](https://github.com/ThegJYang/ns-project).

## Contents

- `NumSemigroups/Basic.lean` — computational core: `canMake`, `frobeniusUpTo`, dual-verified with `decide` + `native_decide`
- `NumSemigroups/PaperClaims.lean` — audit-thread Lean checks for published papers
- `NumSemigroups/Defs.lean`, `Factorization.lean`, `Elasticity.lean` — numerical semigroups, factorizations/length sets, and the flagship theorem `elasticity_eq`: ρ(S) = n_max / n_min

Builds cleanly with zero `sorry`s.

## Building

```
lake exe cache get   # pulls prebuilt Mathlib — do this first
lake build
```

Some of this library was drafted with [Aristotle](https://aristotle.harmonic.fun); its output is re-checked by Lean's kernel like everything else, so it can never introduce an unsound step.
