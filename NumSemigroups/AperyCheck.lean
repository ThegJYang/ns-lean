import NumSemigroups.Basic
import NumSemigroups.AperyCorrect
import NumSemigroups.AperyComplete

/-!
# Discharging the Apéry certificate by computation

`AperyCorrect.lean` proves that *any* table satisfying `AperyCert` determines
the semigroup.  This file connects that to the actual algorithm: it reads the
table off `aperySet`, states the certificate as a decidable proposition, and
shows the two line up.

The result is that `genusApery gens` is *proved* correct for every concrete
`gens` on which `CertCheck gens` evaluates to `true` — and that check is one
extra relaxation sweep, i.e. it costs the same order as the algorithm itself.
-/

namespace NumSemigroups

-- `decide` on these certificates recurses deeper than the default 512.  This is
-- elaborator stack depth, not kernel trust: raising it changes nothing about
-- what is checked.  Verified sufficient up to `m = 41`.
set_option maxRecDepth 100000

/-- The Apéry table as a total function, reading `none` as `0`.  (Entries are
never `none` on a list of generators with gcd 1; the certificate does not need
to know that, because a `none` entry would simply fail `wmod`.) -/
def aperyW (gens : List Nat) (r : Nat) : Nat :=
  ((aperySet gens (multiplicity gens))[r]!).getD 0

/-- The certificate, as a decidable proposition about the computed table.

Read the clauses as: the modulus is a positive generator, generators are
positive, residue `0` is filled with `0`, each entry sits in its own residue
class, the table is closed under adding a generator, and every nonzero entry is
reachable from a smaller entry. -/
def CertCheck (gens : List Nat) : Prop :=
  0 < multiplicity gens ∧
  multiplicity gens ∈ gens ∧
  (∀ g ∈ gens, 0 < g) ∧
  aperyW gens 0 = 0 ∧
  (∀ r ∈ List.range (multiplicity gens),
      aperyW gens r % multiplicity gens = r) ∧
  (∀ r ∈ List.range (multiplicity gens), ∀ g ∈ gens,
      aperyW gens ((aperyW gens r + g) % multiplicity gens) ≤ aperyW gens r + g) ∧
  (∀ r ∈ List.range (multiplicity gens),
      r = 0 ∨ ∃ g ∈ gens,
        g ≤ aperyW gens r ∧
        aperyW gens ((aperyW gens r - g) % multiplicity gens) = aperyW gens r - g)

instance instDecidableCertCheck (gens : List Nat) : Decidable (CertCheck gens) := by
  unfold CertCheck
  infer_instance

/-- A passing check yields the abstract certificate. -/
theorem cert_of_check (gens : List Nat) (h : CertCheck gens) :
    AperyCert gens (multiplicity gens) (aperyW gens) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact
    { mpos := h1
      mgen := h2
      gpos := h3
      wzero := h4
      wmod := fun r hr => h5 r (List.mem_range.mpr hr)
      closed := fun r hr => h6 r (List.mem_range.mpr hr)
      pred := fun r hr hr0 => (h7 r (List.mem_range.mpr hr)).resolve_left hr0 }

/-- The executable definition, unfolded.  Both sides are the same term. -/
lemma genusApery_eq_foldl (gens : List Nat) :
    genusApery gens
      = (List.range (multiplicity gens)).foldl
          (fun acc r => acc + aperyW gens r / multiplicity gens) 0 := rfl

/-! ## The main theorem -/

/-- **`genusApery` computes the genus.**

For any generator list passing the certificate check, the number of natural
numbers *not* representable as a non-negative combination of the generators is
exactly what `genusApery` returns. -/
theorem genusApery_eq_ncard_gaps (gens : List Nat) (h : CertCheck gens) :
    Set.ncard {n : ℕ | ¬ InSG gens n} = genusApery gens := by
  have hc := cert_of_check gens h
  rw [hc.genus, genusApery_eq_foldl, foldl_range_add]
  simp

/-- The gap set is finite whenever the check passes. -/
theorem gaps_finite_of_check (gens : List Nat) (h : CertCheck gens) :
    {n : ℕ | ¬ InSG gens n}.Finite :=
  (cert_of_check gens h).gaps_finite

/-- **The Frobenius number**, stated against the largest table entry.  The link
to the executable `frobeniusNumber` is `frobeniusNumber_isGreatest` below. -/
theorem frobenius_isGreatest_maxW (gens : List Nat) (h : CertCheck gens)
    (hmW : multiplicity gens ≤ maxW (multiplicity gens) (aperyW gens)) :
    IsGreatest {n : ℕ | ¬ InSG gens n}
      (maxW (multiplicity gens) (aperyW gens) - multiplicity gens) :=
  (cert_of_check gens h).frobenius hmW

/-! ## Bridging the executable `frobeniusNumber`

`AperyCorrect.frobenius` is stated about `maxW`, which is a `Finset.sup` and so
noncomputable.  `frobeniusNumber` in `Basic.lean` instead folds `Nat.max` over
the residues, skipping residue `0`.  These lemmas show the two agree, which is
what lets a Frobenius claim be stated about the semigroup rather than about the
program's output. -/

lemma foldr_max_init (a : ℕ) : ∀ l : List ℕ,
    l.foldr Nat.max a = Nat.max a (l.foldr Nat.max 0) := by
  intro l
  induction l with
  | nil => simp
  | cons x t ih =>
      simp only [List.foldr_cons, ih]
      exact Nat.max_left_comm x a _

lemma sup_range_eq_foldr (w : ℕ → ℕ) : ∀ m : ℕ,
    (Finset.range m).sup w = ((List.range m).map w).foldr Nat.max 0 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      -- proved by extensionality rather than by name, since the library lemma
      -- here has been called both `Finset.range_succ` and `Finset.range_add_one`
      have hins : Finset.range (m+1) = insert m (Finset.range m) := by
        ext x
        simp only [Finset.mem_range, Finset.mem_insert]
        omega
      rw [hins, Finset.sup_insert, List.range_succ, List.map_append, List.foldr_append]
      simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil]
      rw [foldr_max_init, ← ih]
      simp

/-- Skipping residue `0` is harmless, because its entry is `0`. -/
lemma foldr_drop1 (w : ℕ → ℕ) (h0 : w 0 = 0) : ∀ m : ℕ,
    (((List.range m).drop 1).map w).foldr Nat.max 0
      = ((List.range m).map w).foldr Nat.max 0 := by
  intro m
  cases m with
  | zero => simp
  | succ m =>
      rw [List.range_succ_eq_map]
      simp only [List.drop_succ_cons, List.drop_zero, List.map_cons, List.foldr_cons, h0]
      exact (Nat.zero_max _).symm

theorem foldr_drop1_eq_maxW (w : ℕ → ℕ) (h0 : w 0 = 0) (m : ℕ) :
    (((List.range m).drop 1).map w).foldr Nat.max 0 = maxW m w := by
  rw [foldr_drop1 w h0, maxW, sup_range_eq_foldr]

/-- The largest Apéry entry, computably.  Same number as `maxW`, but usable by
`decide`. -/
def maxWc (gens : List Nat) : Nat :=
  (((List.range (multiplicity gens)).drop 1).map (aperyW gens)).foldr Nat.max 0

theorem frobeniusNumber_eq_maxWc (gens : List ℕ) :
    frobeniusNumber gens = maxWc gens - multiplicity gens := rfl

theorem maxWc_eq (gens : List ℕ) (h0 : aperyW gens 0 = 0) :
    maxWc gens = maxW (multiplicity gens) (aperyW gens) :=
  foldr_drop1_eq_maxW (aperyW gens) h0 _

theorem frobeniusNumber_eq (gens : List ℕ) (h0 : aperyW gens 0 = 0) :
    frobeniusNumber gens = maxW (multiplicity gens) (aperyW gens) - multiplicity gens := by
  rw [frobeniusNumber_eq_maxWc, maxWc_eq gens h0]

/-! ## The certificate for free, from coprimality

`AperyComplete.basic_apery_cert` proves the certificate holds for every
admissible input, so `CertCheck` need not be evaluated at all.  The hypotheses
below are all cheap: none of them requires computing the Apéry table. -/

theorem cert_of_gcd (gens : List ℕ) (hm : 0 < multiplicity gens)
    (hmg : multiplicity gens ∈ gens) (hpos : ∀ g ∈ gens, 0 < g)
    (hgcd : gens.foldr Nat.gcd 0 = 1) :
    AperyCert gens (multiplicity gens) (aperyW gens) :=
  Complete.basic_apery_cert hm hmg hpos hgcd

/-- **The Frobenius number, as a statement about the semigroup.**

`hmW` excludes the degenerate case where the semigroup is all of `ℕ`. -/
theorem frobeniusNumber_isGreatest (gens : List ℕ) (hm : 0 < multiplicity gens)
    (hmg : multiplicity gens ∈ gens) (hpos : ∀ g ∈ gens, 0 < g)
    (hgcd : gens.foldr Nat.gcd 0 = 1) (hmW : multiplicity gens ≤ maxWc gens) :
    IsGreatest {n : ℕ | ¬ InSG gens n} (frobeniusNumber gens) := by
  have hc := cert_of_gcd gens hm hmg hpos hgcd
  rw [frobeniusNumber_eq gens hc.wzero]
  exact hc.frobenius (by rw [← maxWc_eq gens hc.wzero]; exact hmW)

/-- **The genus, as a statement about the semigroup**, with no certificate to
discharge. -/
theorem genusApery_eq_ncard_gaps_of_gcd (gens : List ℕ) (hm : 0 < multiplicity gens)
    (hmg : multiplicity gens ∈ gens) (hpos : ∀ g ∈ gens, 0 < g)
    (hgcd : gens.foldr Nat.gcd 0 = 1) :
    Set.ncard {n : ℕ | ¬ InSG gens n} = genusApery gens := by
  have hc := cert_of_gcd gens hm hmg hpos hgcd
  rw [hc.genus, genusApery_eq_foldl, foldl_range_add]
  simp

/-! ## Worked instances

Every instance below is discharged by `decide`, so each carries **no extra
axioms at all**: `#print axioms` reports exactly `[propext, Classical.choice,
Quot.sound]`.  No `native_decide`, hence no `Lean.ofReduceBool`.

All five were confirmed against Lean v4.34.0-rc2 with current Mathlib.  The
`m = 41` case takes roughly two minutes to elaborate; the rest are quick. -/

-- ⟨4,7,20⟩ : m = 4.  Kernel-checkable end to end.
example : CertCheck [4, 7, 20] := by decide

theorem genus_4_7_20 : Set.ncard {n : ℕ | ¬ InSG [4, 7, 20] n} = 9 := by
  rw [genusApery_eq_ncard_gaps [4, 7, 20] (by decide)]
  decide

-- ⟨5,11,23⟩ : m = 5.
theorem genus_5_11_23 : Set.ncard {n : ℕ | ¬ InSG [5, 11, 23] n} = 16 := by
  rw [genusApery_eq_ncard_gaps [5, 11, 23] (by decide)]
  decide

-- ⟨11,35,107⟩ : m = 11.  Discrepancy D4 — the genus the paper gets wrong.
theorem genus_11_35_107 : Set.ncard {n : ℕ | ¬ InSG [11, 35, 107] n} = 140 := by
  rw [genusApery_eq_ncard_gaps [11, 35, 107] (by decide)]
  decide

-- ⟨13,25,49,97⟩ : m = 13.  The second-kind family from D6.
theorem genus_13_25_49_97 : Set.ncard {n : ℕ | ¬ InSG [13, 25, 49, 97] n} = 92 := by
  rw [genusApery_eq_ncard_gaps [13, 25, 49, 97] (by decide)]
  decide

-- ⟨41,251,1511⟩ : m = 41.  D4 at b = 6.
set_option maxHeartbeats 4000000 in
-- The kernel evaluates the whole Apéry table twice here, once for the
-- certificate and once for the genus.  The default 200000 heartbeats is not
-- enough; when it runs out Lean reports a `whnf` timeout and the theorem
-- silently falls back to `sorryAx`.  Raising the budget changes nothing about
-- what is checked -- it is a fuel limit, not a trust assumption -- but this
-- declaration takes a couple of minutes to compile.
theorem genus_41_251_1511 : Set.ncard {n : ℕ | ¬ InSG [41, 251, 1511] n} = 4400 := by
  rw [genusApery_eq_ncard_gaps [41, 251, 1511] (by decide)]
  decide

#print axioms genus_4_7_20
#print axioms genus_5_11_23
#print axioms genus_11_35_107
#print axioms genus_13_25_49_97
#print axioms genus_41_251_1511

end NumSemigroups
