# ns-lean

Lean 4 / Mathlib library for numerical semigroups — the S.-T. Yau High School Science Award
project *Numerical Semigroups, Formalized*.

## What's a numerical semigroup?

Say you have coins worth 3, 5, and 7. Which totals can you pay exactly? You can make
0, 3, 5, 6, 7, 8, … — everything from 5 upward — but never 1, 2, or 4. The set of makeable
totals, ⟨3, 5, 7⟩, is a *numerical semigroup*: a set of non-negative integers containing 0,
closed under addition, whose complement (the *gaps* — here {1, 2, 4}) is finite. The largest
gap (4) is the *Frobenius number*; the number of gaps (3) is the *genus*.

This library teaches Lean that mathematics, then uses the same machine-checked reasoning to
re-derive (and cross-check against [GAP](https://www.gap-system.org/)'s `numericalsgps`
package) the concrete numbers printed in ~15–20 published papers.

## Contents

- `NumSemigroups/Basic.lean` — the executable core (`canMake`, `frobeniusUpTo`, …) used to
  dual-verify claims with `decide` and `native_decide`
- `NumSemigroups/AperyCorrect.lean` — proves that a certificate on an Apéry table determines
  the semigroup: it characterizes membership (`AperyCert.mem_iff`), the Frobenius number
  (`AperyCert.frobenius`), and the genus (`AperyCert.genus`) — all without trusting the
  algorithm that built the table
- `NumSemigroups/AperyComplete.lean` — proves the sweep algorithm that builds the Apéry table
  actually satisfies that certificate
- `NumSemigroups/AperyCheck.lean` — bridges the proved algorithm to the executable functions in
  `Basic.lean`
- `NumSemigroups/PaperClaims.lean` — the audit thread: machine-checked claims transcribed from
  published papers, cross-checked against GAP
- `audit.lean` — `#print axioms` over every theorem above, confirming the proofs rest on nothing
  but `propext`, `Classical.choice`, and `Quot.sound` (run with `lake env lean audit.lean`, not
  part of the build)

Builds cleanly with zero `sorry`s. The write-up, GAP scripts, and the audit results table
(including confirmed discrepancies in the literature) live in the companion repo:
[ns-project](https://github.com/ThegJYang/ns-project).

## Building

```
lake exe cache get   # pulls prebuilt Mathlib — do this first
lake build
```

Some of this library was drafted with [Aristotle](https://aristotle.harmonic.fun); its output is
re-checked by Lean's kernel like everything else, so it can never introduce an unsound step.
