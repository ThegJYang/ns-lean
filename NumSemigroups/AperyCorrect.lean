import Mathlib

/-!
# Correctness of the Apéry-set core

This file proves that an Apéry table satisfying a small, *decidable* certificate
really does determine the numerical semigroup: it characterises membership,
pins down the Frobenius number, and counts the gaps.

The point of the certificate is that we never have to prove the Bellman–Ford
sweep correct.  We only have to check, after the fact, four cheap properties of
the array it produced.  All the mathematics lives here; the algorithm is
untrusted.

Main results:

* `AperyCert.mem_iff`     — `n ∈ S ↔ w (n % m) ≤ n`
* `AperyCert.frobenius`   — the Frobenius number is `max w - m`
* `AperyCert.genus`       — the genus is `∑ r < m, w r / m`
-/

namespace NumSemigroups

open Finset

/-! ## The semigroup -/

/-- `InSG gens n` : `n` is a non-negative integer combination of `gens`. -/
inductive InSG (gens : List ℕ) : ℕ → Prop
  | zero : InSG gens 0
  | step {g n : ℕ} (hg : g ∈ gens) (hn : InSG gens n) : InSG gens (g + n)

/-- Adding any multiple of a generator keeps us inside the semigroup. -/
lemma InSG.add_mul_gen {gens : List ℕ} {m : ℕ} (hm : m ∈ gens) (k : ℕ) {x : ℕ}
    (hx : InSG gens x) : InSG gens (x + k * m) := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      have h := InSG.step hm ih
      have e : m + (x + k * m) = x + (k + 1) * m := by ring
      rwa [e] at h

/-! ## The certificate -/

/-- A certificate that `w : ℕ → ℕ` is the Apéry function of `gens` with respect
to the generator `m`: `w r` is the least element of the semigroup congruent to
`r` mod `m`.

Every field is a bounded, decidable statement, so a concrete instance can be
discharged by `decide` / `native_decide`.  Crucially, none of them mentions the
algorithm that produced `w`. -/
structure AperyCert (gens : List ℕ) (m : ℕ) (w : ℕ → ℕ) : Prop where
  /-- The modulus is positive. -/
  mpos : 0 < m
  /-- The modulus is itself a generator. -/
  mgen : m ∈ gens
  /-- All generators are positive. -/
  gpos : ∀ g ∈ gens, 0 < g
  /-- Residue `0` is represented by `0`. -/
  wzero : w 0 = 0
  /-- `w r` lies in residue class `r`. -/
  wmod : ∀ r < m, w r % m = r
  /-- The table is closed under adding a generator: this is what forces `w` to be
  *small* enough.  It is the fixed-point property of the relaxation. -/
  closed : ∀ r < m, ∀ g ∈ gens, w ((w r + g) % m) ≤ w r + g
  /-- Every nonzero entry has a predecessor in the table: this is what forces `w`
  to be *large* enough, i.e. to consist of genuine semigroup elements. -/
  pred : ∀ r < m, r ≠ 0 → ∃ g ∈ gens, g ≤ w r ∧ w ((w r - g) % m) = w r - g

variable {gens : List ℕ} {m : ℕ} {w : ℕ → ℕ}

/-! ## Soundness: every table entry is a semigroup element -/

/-- Every entry of a certified table lies in the semigroup.

The proof is strong induction on the *value*: `pred` hands back a strictly
smaller entry, since generators are positive. -/
theorem AperyCert.mem_of_lt (hc : AperyCert gens m w) : ∀ r < m, InSG gens (w r) := by
  have key : ∀ v : ℕ, ∀ r < m, w r = v → InSG gens v := by
    intro v
    induction v using Nat.strong_induction_on with
    | _ v ih =>
      intro r hr hv
      by_cases hr0 : r = 0
      · subst hr0
        have : v = 0 := by rw [← hv, hc.wzero]
        subst this
        exact InSG.zero
      · obtain ⟨g, hg, hgle, hpr⟩ := hc.pred r hr hr0
        have hgpos : 0 < g := hc.gpos g hg
        have hr'lt : (w r - g) % m < m := Nat.mod_lt _ hc.mpos
        have hlt : w r - g < v := by omega
        have hsub : InSG gens (w r - g) := by
          have := ih (w r - g) hlt ((w r - g) % m) hr'lt hpr
          exact this
        have hadd : InSG gens (g + (w r - g)) := InSG.step hg hsub
        have e : g + (w r - g) = v := by omega
        rwa [e] at hadd
  intro r hr
  exact key (w r) r hr rfl

/-! ## Minimality: no semigroup element beats its table entry -/

/-- Every semigroup element is at least the table entry for its residue.

The proof is induction on the derivation of `InSG`, and the inductive step is
exactly the `closed` field. -/
theorem AperyCert.le_of_mem (hc : AperyCert gens m w) :
    ∀ {n : ℕ}, InSG gens n → w (n % m) ≤ n := by
  intro n hn
  induction hn with
  | zero => rw [Nat.zero_mod, hc.wzero]
  | @step g n hg _ ih =>
      have hr : n % m < m := Nat.mod_lt _ hc.mpos
      have h1 := hc.closed (n % m) hr g hg
      have h2 : (w (n % m) + g) % m = (g + n) % m := by
        rw [Nat.add_mod (w (n % m)) g m, hc.wmod _ hr, Nat.add_mod g n m,
          Nat.add_comm (g % m) (n % m)]
      calc w ((g + n) % m) = w ((w (n % m) + g) % m) := by rw [h2]
        _ ≤ w (n % m) + g := h1
        _ ≤ n + g := by omega
        _ = g + n := Nat.add_comm n g

/-! ## The membership test -/

/-- **Membership characterisation.**  A number lies in the semigroup exactly when
it is at least the Apéry entry for its residue class.  This single statement is
what all the downstream results are built from. -/
theorem AperyCert.mem_iff (hc : AperyCert gens m w) (n : ℕ) :
    InSG gens n ↔ w (n % m) ≤ n := by
  constructor
  · exact hc.le_of_mem
  · intro hle
    have hr : n % m < m := Nat.mod_lt _ hc.mpos
    have hmod : w (n % m) % m = n % m := hc.wmod _ hr
    have hdvd : m ∣ n - w (n % m) := (Nat.modEq_iff_dvd' hle).mp hmod
    obtain ⟨k, hk⟩ := hdvd
    have hbase : InSG gens (w (n % m)) := hc.mem_of_lt _ hr
    have hstep : InSG gens (w (n % m) + k * m) := InSG.add_mul_gen hc.mgen k hbase
    have e : w (n % m) + k * m = n := by
      rw [Nat.mul_comm k m, ← hk, Nat.add_sub_cancel' hle]
    rwa [e] at hstep

/-- The complementary form: `n` is a gap exactly when it falls below its entry. -/
theorem AperyCert.not_mem_iff (hc : AperyCert gens m w) (n : ℕ) :
    ¬ InSG gens n ↔ n < w (n % m) := by
  rw [hc.mem_iff n]; omega

/-! ## The Frobenius number -/

/-- Shorthand for the largest table entry. -/
noncomputable def maxW (m : ℕ) (w : ℕ → ℕ) : ℕ := (Finset.range m).sup w

lemma le_maxW (hr : r < m) : w r ≤ maxW m w :=
  Finset.le_sup (f := w) (Finset.mem_range.mpr hr)

lemma exists_eq_maxW (hm : 0 < m) : ∃ r < m, w r = maxW m w := by
  obtain ⟨r, hr, hval⟩ :=
    Finset.exists_mem_eq_sup (Finset.range m) (Finset.nonempty_range_iff.mpr (by omega)) w
  exact ⟨r, Finset.mem_range.mp hr, hval.symm⟩

/-- **The Frobenius number is `max w - m`.**

`IsGreatest S a` says `a ∈ S` and `a` bounds `S` above, so this is exactly the
statement that `max w - m` is the largest gap.  The hypothesis `m ≤ maxW`
excludes the degenerate case where the semigroup is all of `ℕ`. -/
theorem AperyCert.frobenius (hc : AperyCert gens m w) (hmW : m ≤ maxW m w) :
    IsGreatest {n : ℕ | ¬ InSG gens n} (maxW m w - m) := by
  obtain ⟨r₀, hr₀, hval⟩ := exists_eq_maxW (w := w) hc.mpos
  constructor
  · -- `maxW - m` is a gap
    show ¬ InSG gens (maxW m w - m)
    rw [hc.not_mem_iff]
    have hmod : (maxW m w - m) % m = r₀ := by
      have : (maxW m w - m) % m = maxW m w % m := by
        conv_rhs => rw [← Nat.sub_add_cancel hmW]
        rw [Nat.add_mod_right]
      rw [this, ← hval, hc.wmod r₀ hr₀]
    rw [hmod, hval]
    omega
  · -- nothing bigger is a gap
    intro n hn
    rw [Set.mem_setOf_eq, hc.not_mem_iff] at hn
    by_contra hcon
    push_neg at hcon
    have hr : n % m < m := Nat.mod_lt _ hc.mpos
    have hub : w (n % m) ≤ maxW m w := le_maxW hr
    have hmodeq : n % m = w (n % m) % m := (hc.wmod _ hr).symm
    have hdvd : m ∣ w (n % m) - n := (Nat.modEq_iff_dvd' (le_of_lt hn)).mp hmodeq
    have hge : m ≤ w (n % m) - n := Nat.le_of_dvd (by omega) hdvd
    omega

/-! ## The genus -/

/-- The gaps, as a `Finset`.  Everything below `maxW` that falls under its own
Apéry entry. -/
noncomputable def gapsF (m : ℕ) (w : ℕ → ℕ) : Finset ℕ :=
  (Finset.range (maxW m w)).filter (fun n => n < w (n % m))

lemma AperyCert.mem_gapsF (hc : AperyCert gens m w) (n : ℕ) :
    n ∈ gapsF m w ↔ ¬ InSG gens n := by
  rw [gapsF, Finset.mem_filter, Finset.mem_range, hc.not_mem_iff]
  constructor
  · exact fun h => h.2
  · intro h
    have hr : n % m < m := Nat.mod_lt _ hc.mpos
    have := le_maxW (w := w) hr
    exact ⟨by omega, h⟩

/-- The fibre of the residue map over `r` has exactly `w r / m` elements: it is
`{r, r + m, r + 2m, …}` truncated at `w r`. -/
lemma AperyCert.fiber_card (hc : AperyCert gens m w) (r : ℕ) (hr : r < m) :
    ((gapsF m w).filter (fun n => n % m = r)).card = w r / m := by
  have hwr : w r % m = r := hc.wmod r hr
  have hd2 : w r / m * m + r = w r := by
    conv_rhs => rw [← Nat.div_add_mod (w r) m]
    rw [hwr, Nat.mul_comm]
  have himg : (gapsF m w).filter (fun n => n % m = r)
      = (Finset.range (w r / m)).image (fun q => r + q * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range, gapsF]
    constructor
    · rintro ⟨⟨hnW, hlt⟩, hmodr⟩
      rw [hmodr] at hlt
      have hd1 : n / m * m + r = n := by
        conv_rhs => rw [← Nat.div_add_mod n m]
        rw [hmodr, Nat.mul_comm]
      refine ⟨n / m, ?_, by omega⟩
      by_contra hcon
      push_neg at hcon
      have : w r ≤ n := by
        calc w r = w r / m * m + r := hd2.symm
          _ ≤ n / m * m + r := Nat.add_le_add_right (Nat.mul_le_mul_right m hcon) r
          _ = n := hd1
      omega
    · rintro ⟨q, hq, rfl⟩
      have hmodr : (r + q * m) % m = r := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
      have hstep : (q + 1) * m ≤ w r / m * m := Nat.mul_le_mul_right m hq
      rw [Nat.succ_mul] at hstep
      have hlt : r + q * m < w r := by omega
      have hub : w r ≤ maxW m w := le_maxW hr
      exact ⟨⟨by omega, by rw [hmodr]; omega⟩, hmodr⟩
  rw [himg, Finset.card_image_of_injective _ ?inj, Finset.card_range]
  case inj =>
    intro a b hab
    simp only at hab
    have h : a * m = b * m := by omega
    exact Nat.eq_of_mul_eq_mul_right hc.mpos h

/-- **The genus is `∑ r < m, w r / m`.**

This is the Brauer–Shockley count, written in the form that avoids all
truncated-subtraction and rounding hazards. -/
theorem AperyCert.genus (hc : AperyCert gens m w) :
    Set.ncard {n : ℕ | ¬ InSG gens n} = ∑ r ∈ Finset.range m, w r / m := by
  have hset : {n : ℕ | ¬ InSG gens n} = ↑(gapsF m w) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    rw [← hc.mem_gapsF n]
  rw [hset, Set.ncard_coe_finset]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun n => n % m) (t := Finset.range m)
    (fun x _ => Finset.mem_range.mpr (Nat.mod_lt _ hc.mpos))]
  exact Finset.sum_congr rfl fun r hr => hc.fiber_card r (Finset.mem_range.mp hr)

/-- The gap set is finite — a free by-product, needing no `gcd` argument. -/
theorem AperyCert.gaps_finite (hc : AperyCert gens m w) :
    {n : ℕ | ¬ InSG gens n}.Finite := by
  have hset : {n : ℕ | ¬ InSG gens n} = ↑(gapsF m w) := by
    ext n
    simp only [Set.mem_setOf_eq, Finset.mem_coe]
    rw [← hc.mem_gapsF n]
  rw [hset]
  exact (gapsF m w).finite_toSet

/-! ## Bridging `List.foldl` to `Finset.sum`

`Basic.lean` has no imports, so it accumulates with `List.foldl`.  This lemma
lets the results above be stated about the executable definition. -/

lemma foldl_range_add (f : ℕ → ℕ) :
    ∀ (n a : ℕ), (List.range n).foldl (fun acc r => acc + f r) a
      = a + ∑ r ∈ Finset.range n, f r := by
  intro n
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih]
      omega

end NumSemigroups
