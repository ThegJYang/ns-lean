import NumSemigroups.Basic
import NumSemigroups.AperyCorrect

/-!
# Unconditional correctness of the Apéry algorithm

`AperyCorrect.lean` proves that *any* table satisfying `AperyCert` determines the
semigroup.  `AperyCheck.lean` discharges that certificate by computation for
particular inputs.  Together they give **per-input** verification: each printed
number is checked, but the algorithm itself is never proved correct.

This file closes that gap.  The main result is

  `basic_apery_cert :
     0 < m → m ∈ gens → (∀ g ∈ gens, 0 < g) → gens.foldr Nat.gcd 0 = 1 →
     AperyCert gens m (fun r => ((aperySet gens m)[r]!).getD 0)`

which says the relaxation algorithm produces a certified table for **every**
admissible input.  No check is needed; `CertCheck` can never fail.  Every
hypothesis is elementary: the modulus is a positive generator, the generators
are positive, and they are collectively coprime.

## Structure of the argument

1. *The `m-1` bound* (`short_rep`).  Every semigroup element is matched — same
   residue, no larger value — by one built from fewer than `m` generators.
   Proved by pigeonhole on prefix sums: if two prefix sums agree mod `m`, the
   stretch between them is a cycle in the residue graph and can be deleted.
   This is the classical "cut a cycle out of a minimal representation"
   argument, and it is why `m-1` relaxation rounds suffice.

2. *Coverage* (`covers_iter`).  After `k` rounds, every representation of length
   at most `k` has been accounted for.  Proved by induction on rounds, using a
   monotonicity lemma (relaxation never increases an entry) and a propagation
   lemma (a sweep that passes residue `r` pushes its value along every
   generator).

3. *Soundness* (`apery_sound`).  Every filled entry is a genuine semigroup
   element lying in its own residue class.  An invariant maintained through
   every write.

4. Combining (1) and (2) gives minimality (`apery_min`); with (3) that yields
   all seven certificate fields.

5. *Reachability* (`hsurj_of_gcd`).  The intermediate results assume every
   residue class is represented — equivalently, that the semigroup is
   numerical.  That assumption is necessary (without it some entries stay
   `none` for ever and the gap set is infinite), but it need not be assumed:
   it follows from the generators being coprime, via a subgroup-of-`ZMod m`
   argument and Bézout.

## Bridge to `Basic.lean`

The relaxation machinery here is stated in named pieces rather than the nested
lambdas of `Basic.lean`.  The `rfl` near the bottom confirms the two are the
*same term*, so `basic_apery_cert` applies to the code that actually runs.

Verified against Lean v4.34.0-rc2 with current Mathlib.  All results depend on
`[propext, Classical.choice, Quot.sound]` and nothing else.
-/

namespace NumSemigroups

/-! Everything below lives in a nested namespace, so the names introduced for the
proof (`aperySet`, `relaxRound`, `aperyW`, ...) cannot collide with the
executable ones at the root or with `AperyCheck.lean`.  `InSG` and `AperyCert`
come from `AperyCorrect.lean` and are visible here unqualified. -/

namespace Complete

/-! ## Semigroup elements as lists of generators

Working with an explicit list, rather than the inductive derivation, is what
makes the pigeonhole argument possible: a list has positions to compare. -/

/-- Any list of generators sums into the semigroup. -/
lemma insg_of_list {gens : List ℕ} :
    ∀ {l : List ℕ}, (∀ x ∈ l, x ∈ gens) → InSG gens l.sum := by
  intro l
  induction l with
  | nil => intro _; simpa using InSG.zero
  | cons a t ih =>
      intro hl
      have ha : a ∈ gens := hl a (by simp)
      have ht : ∀ x ∈ t, x ∈ gens := fun x hx => hl x (by simp [hx])
      have h := InSG.step ha (ih ht)
      simpa [List.sum_cons] using h

/-- Conversely, every semigroup element is the sum of some list of generators. -/
lemma list_of_insg {gens : List ℕ} {n : ℕ} (h : InSG gens n) :
    ∃ l : List ℕ, (∀ x ∈ l, x ∈ gens) ∧ l.sum = n := by
  induction h with
  | zero => exact ⟨[], by simp, by simp⟩
  | @step g n hg hn ih =>
      obtain ⟨l, hl, hsum⟩ := ih
      refine ⟨g :: l, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hg
        · exact hl x hx
      · simp [hsum]

/-! ## Part 1: the `m-1` bound -/

/-- With positive entries, the prefix sums of a list strictly increase.
Positivity of the generators is exactly what makes cutting a cycle a strict
improvement. -/
lemma sum_take_strictMono {l : List ℕ} (hpos : ∀ x ∈ l, 0 < x) :
    ∀ {i j : ℕ}, i < j → j ≤ l.length → (l.take i).sum < (l.take j).sum := by
  intro i j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
      intro hij hj
      have hjl : j < l.length := by omega
      have hstep : (l.take (j+1)).sum = (l.take j).sum + l[j] := List.sum_take_succ l j hjl
      have hp : 0 < l[j] := hpos _ (List.getElem_mem hjl)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with h | h
      · have := ih h (by omega)
        omega
      · subst h
        omega

/-- If two prefix sums agree mod `m`, the stretch between them is a cycle in the
residue graph and can be deleted: the result is shorter, strictly smaller, and
lands in the same residue class. -/
lemma cut_once {gens : List ℕ} {m : ℕ} (_hm : 0 < m) (hpos : ∀ g ∈ gens, 0 < g)
    (l : List ℕ) (hl : ∀ x ∈ l, x ∈ gens) {i j : ℕ}
    (hij : i < j) (hj : j ≤ l.length)
    (hmod : (l.take i).sum % m = (l.take j).sum % m) :
    ∃ l2 : List ℕ, (∀ x ∈ l2, x ∈ gens) ∧ l2.length < l.length ∧ l2.sum < l.sum ∧
      l2.sum % m = l.sum % m := by
  have hlpos : ∀ x ∈ l, 0 < x := fun x hx => hpos x (hl x hx)
  have hsplit : (l.take j).sum + (l.drop j).sum = l.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hstrict : (l.take i).sum < (l.take j).sum := sum_take_strictMono hlpos hij hj
  refine ⟨l.take i ++ l.drop j, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hl x (List.mem_of_mem_take h)
    · exact hl x (List.mem_of_mem_drop h)
  · have h1 : (l.take i ++ l.drop j).length = i + (l.length - j) := by
      simp [List.length_take, List.length_drop]
      omega
    omega
  · have h2 : (l.take i ++ l.drop j).sum = (l.take i).sum + (l.drop j).sum := List.sum_append
    omega
  · have h2 : (l.take i ++ l.drop j).sum = (l.take i).sum + (l.drop j).sum := List.sum_append
    rw [h2, ← hsplit, Nat.add_mod, hmod, ← Nat.add_mod]

/-- Repeatedly cutting brings any representation below length `m`.  The bound
`N` is what the induction runs on; each cut strictly shortens the list. -/
lemma exists_short {gens : List ℕ} {m : ℕ} (hm : 0 < m) (hpos : ∀ g ∈ gens, 0 < g) :
    ∀ N : ℕ, ∀ l : List ℕ, l.length ≤ N → (∀ x ∈ l, x ∈ gens) →
      ∃ l2 : List ℕ, (∀ x ∈ l2, x ∈ gens) ∧ l2.length < m ∧ l2.sum ≤ l.sum ∧
        l2.sum % m = l.sum % m := by
  intro N
  induction N with
  | zero =>
      intro l hlen hl
      exact ⟨l, hl, by omega, le_refl _, rfl⟩
  | succ N ih =>
      intro l hlen hl
      by_cases hshort : l.length < m
      · exact ⟨l, hl, hshort, le_refl _, rfl⟩
      · have hge : m ≤ l.length := by omega
        have hcard : (Finset.range m).card < (Finset.range (l.length + 1)).card := by
          simp only [Finset.card_range]
          omega
        -- Pigeonhole: among the `l.length + 1` prefix sums, two share a residue.
        obtain ⟨i, hi, j, hj, hne, hfe⟩ :=
          Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
            (f := fun k => (l.take k).sum % m)
            (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hm))
        rw [Finset.mem_range] at hi hj
        rcases Nat.lt_or_ge i j with hij | hij
        · obtain ⟨l2, h1, h2, h3, h4⟩ := cut_once hm hpos l hl hij (by omega) hfe
          obtain ⟨l3, k1, k2, k3, k4⟩ := ih l2 (by omega) h1
          exact ⟨l3, k1, k2, by omega, by rw [k4, h4]⟩
        · have hji : j < i := by omega
          obtain ⟨l2, h1, h2, h3, h4⟩ := cut_once hm hpos l hl hji (by omega) hfe.symm
          obtain ⟨l3, k1, k2, k3, k4⟩ := ih l2 (by omega) h1
          exact ⟨l3, k1, k2, by omega, by rw [k4, h4]⟩

/-- **The `m-1` bound.**  Every semigroup element is matched, in residue and
without increase in value, by one built from fewer than `m` generators.

This is why `m-1` rounds of relaxation are enough. -/
theorem short_rep {gens : List ℕ} {m : ℕ} (hm : 0 < m) (hpos : ∀ g ∈ gens, 0 < g)
    {n : ℕ} (hn : InSG gens n) :
    ∃ l : List ℕ, (∀ x ∈ l, x ∈ gens) ∧ l.length < m ∧ l.sum ≤ n ∧ l.sum % m = n % m := by
  obtain ⟨l, hl, hsum⟩ := list_of_insg hn
  obtain ⟨l2, h1, h2, h3, h4⟩ := exists_short hm hpos l.length l le_rfl hl
  exact ⟨l2, h1, h2, by omega, by rw [h4, hsum]⟩

/-! ## Part 2: ordering on table entries -/

/-- `OLe x y` : `x` is at least as good as `y`, where `none` is worst. -/
def OLe (x y : Option ℕ) : Prop :=
  match y with
  | none => True
  | some b => ∃ a, x = some a ∧ a ≤ b

lemma OLe_none (x : Option ℕ) : OLe x none := by trivial

lemma OLe_refl (x : Option ℕ) : OLe x x := by
  cases x with
  | none => trivial
  | some a => exact ⟨a, rfl, le_refl a⟩

lemma OLe_trans {x y z : Option ℕ} (h1 : OLe x y) (h2 : OLe y z) : OLe x z := by
  cases z with
  | none => trivial
  | some c =>
      obtain ⟨b, hb, hbc⟩ := h2
      subst hb
      obtain ⟨a, ha, hab⟩ := h1
      exact ⟨a, ha, le_trans hab hbc⟩

/-! ## One relaxation step -/

/-- From residue `r` holding value `d`, push along generator `g`. -/
def relaxStep (m r d : ℕ) (acc : Array (Option ℕ)) (g : ℕ) : Array (Option ℕ) :=
  match acc[(r + g) % m]! with
  | none => acc.set! ((r + g) % m) (some (d + g))
  | some cur => if d + g < cur then acc.set! ((r + g) % m) (some (d + g)) else acc

lemma size_relaxStep (m r d : ℕ) (acc : Array (Option ℕ)) (g : ℕ) :
    (relaxStep m r d acc g).size = acc.size := by
  unfold relaxStep
  split
  · exact Array.size_set! _ _ _
  · split
    · exact Array.size_set! _ _ _
    · rfl

/-- Relaxation never makes an entry worse. -/
lemma relaxStep_mono (m r d : ℕ) (hm : 0 < m) (acc : Array (Option ℕ))
    (hsz : acc.size = m) (g j : ℕ) :
    OLe (relaxStep m r d acc g)[j]! acc[j]! := by
  have hlt : (r + g) % m < acc.size := by rw [hsz]; exact Nat.mod_lt _ hm
  cases hcur : acc[(r + g) % m]! with
  | none =>
      simp only [relaxStep, hcur]
      by_cases hj : j = (r + g) % m
      · subst hj; rw [hcur]; trivial
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)]
        exact OLe_refl _
  | some cur =>
      simp only [relaxStep, hcur]
      by_cases hd : d + g < cur
      · simp only [hd, if_true]
        by_cases hj : j = (r + g) % m
        · subst hj
          rw [Array.getElem!_set!_self _ _ _ hlt, hcur]
          exact ⟨d + g, rfl, le_of_lt hd⟩
        · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)]
          exact OLe_refl _
      · simp only [hd, if_false]
        exact OLe_refl _

/-- After the step, the target residue holds at most `d + g`. -/
lemma relaxStep_at (m r d : ℕ) (hm : 0 < m) (acc : Array (Option ℕ))
    (hsz : acc.size = m) (g : ℕ) :
    OLe (relaxStep m r d acc g)[(r + g) % m]! (some (d + g)) := by
  have hlt : (r + g) % m < acc.size := by rw [hsz]; exact Nat.mod_lt _ hm
  cases hcur : acc[(r + g) % m]! with
  | none =>
      simp only [relaxStep, hcur]
      rw [Array.getElem!_set!_self _ _ _ hlt]
      exact ⟨d + g, rfl, le_refl _⟩
  | some cur =>
      simp only [relaxStep, hcur]
      by_cases hd : d + g < cur
      · simp only [hd, if_true]
        rw [Array.getElem!_set!_self _ _ _ hlt]
        exact ⟨d + g, rfl, le_refl _⟩
      · simp only [hd, if_false]
        rw [hcur]
        exact ⟨cur, rfl, by omega⟩

/-! ## Folding over the generators -/

lemma size_foldl_gens (m r d : ℕ) : ∀ (gens : List ℕ) (dist : Array (Option ℕ)),
    (List.foldl (relaxStep m r d) dist gens).size = dist.size := by
  intro gens
  induction gens with
  | nil => intro dist; simp only [List.foldl_nil]
  | cons g t ih => intro dist; rw [List.foldl_cons, ih, size_relaxStep]

lemma foldl_gens_mono (m r d : ℕ) (hm : 0 < m) :
    ∀ (gens : List ℕ) (dist : Array (Option ℕ)), dist.size = m →
      ∀ (j : ℕ), OLe (List.foldl (relaxStep m r d) dist gens)[j]! dist[j]! := by
  intro gens
  induction gens with
  | nil => intro dist hsz j; simp only [List.foldl_nil]; exact OLe_refl _
  | cons g t ih =>
      intro dist hsz j
      rw [List.foldl_cons]
      have h1 : (relaxStep m r d dist g).size = m := by rw [size_relaxStep, hsz]
      exact OLe_trans (ih _ h1 j) (relaxStep_mono m r d hm dist hsz g j)

lemma foldl_gens_at (m r d : ℕ) (hm : 0 < m) :
    ∀ (gens : List ℕ) (dist : Array (Option ℕ)), dist.size = m →
      ∀ g ∈ gens, OLe (List.foldl (relaxStep m r d) dist gens)[(r + g) % m]! (some (d + g)) := by
  intro gens
  induction gens with
  | nil => intro dist hsz g hg; simp at hg
  | cons a t ih =>
      intro dist hsz g hg
      rw [List.foldl_cons]
      have h1 : (relaxStep m r d dist a).size = m := by rw [size_relaxStep, hsz]
      rcases List.mem_cons.mp hg with rfl | hg2
      · exact OLe_trans (foldl_gens_mono m r d hm t _ h1 _) (relaxStep_at m r d hm dist hsz g)
      · exact ih _ h1 g hg2

/-! ## One residue -/

def relaxResidue (gens : List ℕ) (m : ℕ) (dist : Array (Option ℕ)) (r : ℕ) : Array (Option ℕ) :=
  match dist[r]! with
  | none => dist
  | some d => List.foldl (relaxStep m r d) dist gens

lemma size_relaxResidue (gens : List ℕ) (m : ℕ) (dist : Array (Option ℕ)) (r : ℕ) :
    (relaxResidue gens m dist r).size = dist.size := by
  cases hd : dist[r]! with
  | none => simp only [relaxResidue, hd]
  | some d => simp only [relaxResidue, hd]; exact size_foldl_gens m r d gens dist

lemma relaxResidue_mono (gens : List ℕ) (m : ℕ) (hm : 0 < m) (dist : Array (Option ℕ))
    (hsz : dist.size = m) (r j : ℕ) :
    OLe (relaxResidue gens m dist r)[j]! dist[j]! := by
  cases hd : dist[r]! with
  | none => simp only [relaxResidue, hd]; exact OLe_refl _
  | some d => simp only [relaxResidue, hd]; exact foldl_gens_mono m r d hm gens dist hsz j

lemma relaxResidue_at (gens : List ℕ) (m : ℕ) (hm : 0 < m) (dist : Array (Option ℕ))
    (hsz : dist.size = m) (r d : ℕ) (hr : OLe dist[r]! (some d)) (g : ℕ) (hg : g ∈ gens) :
    OLe (relaxResidue gens m dist r)[(r + g) % m]! (some (d + g)) := by
  obtain ⟨d0, hd0, hle⟩ := hr
  simp only [relaxResidue, hd0]
  obtain ⟨a, ha, hab⟩ := foldl_gens_at m r d0 hm gens dist hsz g hg
  exact ⟨a, ha, by omega⟩

/-! ## One full round -/

lemma size_foldl_res (gens : List ℕ) (m : ℕ) : ∀ (rs : List ℕ) (dist : Array (Option ℕ)),
    (List.foldl (relaxResidue gens m) dist rs).size = dist.size := by
  intro rs
  induction rs with
  | nil => intro dist; simp only [List.foldl_nil]
  | cons a t ih => intro dist; rw [List.foldl_cons, ih, size_relaxResidue]

lemma foldl_res_mono (gens : List ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ (rs : List ℕ) (dist : Array (Option ℕ)), dist.size = m →
      ∀ (j : ℕ), OLe (List.foldl (relaxResidue gens m) dist rs)[j]! dist[j]! := by
  intro rs
  induction rs with
  | nil => intro dist hsz j; simp only [List.foldl_nil]; exact OLe_refl _
  | cons a t ih =>
      intro dist hsz j
      rw [List.foldl_cons]
      have h1 : (relaxResidue gens m dist a).size = m := by rw [size_relaxResidue, hsz]
      exact OLe_trans (ih _ h1 j) (relaxResidue_mono gens m hm dist hsz a j)

/-- The key propagation step: if residue `r` is in the list being swept and holds
a value at most `d`, then after the sweep residue `r + g` holds at most `d + g`. -/
lemma foldl_res_at (gens : List ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ (rs : List ℕ) (dist : Array (Option ℕ)), dist.size = m →
      ∀ r ∈ rs, ∀ d, OLe dist[r]! (some d) → ∀ g ∈ gens,
        OLe (List.foldl (relaxResidue gens m) dist rs)[(r + g) % m]! (some (d + g)) := by
  intro rs
  induction rs with
  | nil => intro dist hsz r hr; simp at hr
  | cons a t ih =>
      intro dist hsz r hr d hd g hg
      rw [List.foldl_cons]
      have h1 : (relaxResidue gens m dist a).size = m := by rw [size_relaxResidue, hsz]
      rcases List.mem_cons.mp hr with rfl | hr2
      · exact OLe_trans (foldl_res_mono gens m hm t _ h1 _)
          (relaxResidue_at gens m hm dist hsz r d hd g hg)
      · have hd2 : OLe (relaxResidue gens m dist a)[r]! (some d) :=
          OLe_trans (relaxResidue_mono gens m hm dist hsz a r) hd
        exact ih _ h1 r hr2 d hd2 g hg

/-! ## Rounds and coverage -/

def relaxRound (gens : List ℕ) (m : ℕ) (dist : Array (Option ℕ)) : Array (Option ℕ) :=
  (List.range m).foldl (relaxResidue gens m) dist

lemma size_relaxRound (gens : List ℕ) (m : ℕ) (dist : Array (Option ℕ)) :
    (relaxRound gens m dist).size = dist.size := size_foldl_res gens m _ dist

/-- `Covers gens m k dist` : every representation of length at most `k` has been
accounted for in the table. -/
def Covers (gens : List ℕ) (m k : ℕ) (dist : Array (Option ℕ)) : Prop :=
  ∀ l : List ℕ, (∀ x ∈ l, x ∈ gens) → l.length ≤ k → OLe dist[l.sum % m]! (some l.sum)

lemma covers_step (gens : List ℕ) (m : ℕ) (hm : 0 < m) (k : ℕ) (dist : Array (Option ℕ))
    (hsz : dist.size = m) (hC : Covers gens m k dist) :
    Covers gens m (k+1) (relaxRound gens m dist) := by
  intro l hl hlen
  simp only [relaxRound]
  cases l with
  | nil =>
      exact OLe_trans (foldl_res_mono gens m hm _ dist hsz _)
        (hC [] (by simp) (by simp))
  | cons g t =>
      have hg : g ∈ gens := hl g (by simp)
      have ht : ∀ x ∈ t, x ∈ gens := fun x hx => hl x (by simp [hx])
      have htlen : t.length ≤ k := by simp only [List.length_cons] at hlen; omega
      have hCt := hC t ht htlen
      have hr : t.sum % m ∈ List.range m := List.mem_range.mpr (Nat.mod_lt _ hm)
      have key := foldl_res_at gens m hm (List.range m) dist hsz (t.sum % m) hr t.sum hCt g hg
      have he : (t.sum % m + g) % m = (g :: t).sum % m := by
        rw [Nat.mod_add_mod, List.sum_cons, Nat.add_comm g t.sum]
      rw [← he]
      obtain ⟨a, ha, hab⟩ := key
      refine ⟨a, ha, ?_⟩
      rw [List.sum_cons]
      omega

lemma covers_iter (gens : List ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ (K : ℕ) (dist : Array (Option ℕ)) (k : ℕ), dist.size = m → Covers gens m k dist →
      Covers gens m (k + K) ((List.range K).foldl (fun acc _ => relaxRound gens m acc) dist) := by
  intro K
  induction K with
  | zero => intro dist k hsz hC; simpa using hC
  | succ K ih =>
      intro dist k hsz hC
      rw [List.range_succ, List.foldl_append]
      have hsz2 : ((List.range K).foldl (fun acc _ => relaxRound gens m acc) dist).size = m := by
        clear hC ih
        induction K generalizing dist with
        | zero => simpa using hsz
        | succ K ih2 =>
            rw [List.range_succ, List.foldl_append]
            simp only [List.foldl_cons, List.foldl_nil]
            rw [size_relaxRound]
            exact ih2 dist hsz
      have hinner := ih dist k hsz hC
      simp only [List.foldl_cons, List.foldl_nil]
      have := covers_step gens m hm (k + K) _ hsz2 hinner
      have he : k + (K + 1) = (k + K) + 1 := by omega
      rw [he]
      exact this

/-! ## Soundness -/

lemma replicate_get (m j : ℕ) : (Array.replicate m (none : Option ℕ))[j]! = none := by
  by_cases h : j < (Array.replicate m (none : Option ℕ)).size
  · rw [getElem!_pos (Array.replicate m (none : Option ℕ)) j h]; simp
  · rw [getElem!_neg (Array.replicate m (none : Option ℕ)) j h]; rfl

/-- Every filled entry is a genuine semigroup element in its own class. -/
def Sound (gens : List ℕ) (m : ℕ) (dist : Array (Option ℕ)) : Prop :=
  ∀ r v : ℕ, dist[r]! = some v → InSG gens v ∧ v % m = r % m

/-- A relaxation step either leaves an entry alone or writes `d + g` at the
target residue.  Nothing else can happen. -/
lemma relaxStep_cases (m r d : ℕ) (hm : 0 < m) (acc : Array (Option ℕ))
    (hsz : acc.size = m) (g j : ℕ) :
    (relaxStep m r d acc g)[j]! = acc[j]! ∨
      ((relaxStep m r d acc g)[j]! = some (d + g) ∧ j = (r + g) % m) := by
  have hlt : (r + g) % m < acc.size := by rw [hsz]; exact Nat.mod_lt _ hm
  by_cases hj : j = (r + g) % m
  · cases hcur : acc[(r + g) % m]! with
    | none =>
        right
        refine ⟨?_, hj⟩
        simp only [relaxStep, hcur]
        rw [hj, Array.getElem!_set!_self _ _ _ hlt]
    | some cur =>
        by_cases hd2 : d + g < cur
        · right
          refine ⟨?_, hj⟩
          simp only [relaxStep, hcur]
          rw [if_pos hd2, hj, Array.getElem!_set!_self _ _ _ hlt]
        · left
          simp only [relaxStep, hcur]
          rw [if_neg hd2]
  · left
    simp only [relaxStep]
    split
    · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)]
    · split
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)]
      · rfl

lemma relaxStep_sound (gens : List ℕ) (m r d : ℕ) (hm : 0 < m) (acc : Array (Option ℕ))
    (hsz : acc.size = m) (hS : Sound gens m acc) (hd : InSG gens d) (hdr : d % m = r % m)
    (g : ℕ) (hg : g ∈ gens) : Sound gens m (relaxStep m r d acc g) := by
  intro j v hv
  rcases relaxStep_cases m r d hm acc hsz g j with h | ⟨h, hj⟩
  · exact hS j v (by rw [← h]; exact hv)
  · rw [h] at hv
    have hveq : v = d + g := (Option.some.inj hv).symm
    subst hveq
    subst hj
    constructor
    · have := InSG.step hg hd
      rwa [Nat.add_comm] at this
    · rw [Nat.mod_mod, Nat.add_mod d g m, hdr, ← Nat.add_mod]

lemma foldl_gens_sound (gens : List ℕ) (m r d : ℕ) (hm : 0 < m)
    (hd : InSG gens d) (hdr : d % m = r % m) :
    ∀ (gs : List ℕ), (∀ x ∈ gs, x ∈ gens) → ∀ (acc : Array (Option ℕ)), acc.size = m →
      Sound gens m acc → Sound gens m (List.foldl (relaxStep m r d) acc gs) := by
  intro gs
  induction gs with
  | nil => intro _ acc _ hS; simpa using hS
  | cons a t ih =>
      intro hgs acc hsz hS
      rw [List.foldl_cons]
      have ha : a ∈ gens := hgs a (by simp)
      have ht : ∀ x ∈ t, x ∈ gens := fun x hx => hgs x (by simp [hx])
      have h1 : (relaxStep m r d acc a).size = m := by rw [size_relaxStep, hsz]
      exact ih ht _ h1 (relaxStep_sound gens m r d hm acc hsz hS hd hdr a ha)

lemma relaxResidue_sound (gens : List ℕ) (m : ℕ) (hm : 0 < m) (_hgens : ∀ x ∈ gens, x ∈ gens)
    (dist : Array (Option ℕ)) (hsz : dist.size = m) (hS : Sound gens m dist) (r : ℕ) :
    Sound gens m (relaxResidue gens m dist r) := by
  cases hd : dist[r]! with
  | none => simp only [relaxResidue, hd]; exact hS
  | some d =>
      simp only [relaxResidue, hd]
      obtain ⟨hdSG, hdmod⟩ := hS r d hd
      exact foldl_gens_sound gens m r d hm hdSG hdmod gens (fun x hx => hx) dist hsz hS

lemma foldl_res_sound (gens : List ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ (rs : List ℕ) (dist : Array (Option ℕ)), dist.size = m → Sound gens m dist →
      Sound gens m (List.foldl (relaxResidue gens m) dist rs) := by
  intro rs
  induction rs with
  | nil => intro dist _ hS; simpa using hS
  | cons a t ih =>
      intro dist hsz hS
      rw [List.foldl_cons]
      have h1 : (relaxResidue gens m dist a).size = m := by rw [size_relaxResidue, hsz]
      exact ih _ h1 (relaxResidue_sound gens m hm (fun x hx => hx) dist hsz hS a)

/-! ## The algorithm -/

def initA (m : ℕ) : Array (Option ℕ) := (Array.replicate m none).set! 0 (some 0)

def aperySet (gens : List ℕ) (m : ℕ) : Array (Option ℕ) :=
  (List.range (m - 1)).foldl (fun acc _ => relaxRound gens m acc) (initA m)

lemma size_initA (m : ℕ) : (initA m).size = m := by
  simp only [initA, Array.size_set!, Array.size_replicate]

lemma initA_zero (m : ℕ) (hm : 0 < m) : (initA m)[0]! = some 0 := by
  have hlt : 0 < (Array.replicate m (none : Option ℕ)).size := by
    rw [Array.size_replicate]; omega
  simp only [initA]
  rw [Array.getElem!_set!_self _ _ _ hlt]

lemma initA_ne (m j : ℕ) (hj : j ≠ 0) : (initA m)[j]! = none := by
  simp only [initA]
  rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)]
  exact replicate_get m j

lemma initA_sound (gens : List ℕ) (m : ℕ) (hm : 0 < m) : Sound gens m (initA m) := by
  intro r v hv
  by_cases hr : r = 0
  · subst hr
    rw [initA_zero m hm] at hv
    have hv0 : v = 0 := (Option.some.inj hv).symm
    subst hv0
    exact ⟨InSG.zero, rfl⟩
  · rw [initA_ne m r hr] at hv
    exact absurd hv (by simp)

lemma initA_covers (gens : List ℕ) (m : ℕ) (hm : 0 < m) : Covers gens m 0 (initA m) := by
  intro l hl hlen
  cases l with
  | nil =>
      simp only [List.sum_nil, Nat.zero_mod]
      rw [initA_zero m hm]
      exact ⟨0, rfl, le_refl 0⟩
  | cons a t => simp only [List.length_cons] at hlen; omega

lemma size_iter (gens : List ℕ) (m : ℕ) : ∀ (K : ℕ) (dist : Array (Option ℕ)),
    ((List.range K).foldl (fun acc _ => relaxRound gens m acc) dist).size = dist.size := by
  intro K
  induction K with
  | zero => intro dist; simp only [List.range_zero, List.foldl_nil]
  | succ K ih =>
      intro dist
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [size_relaxRound, ih]

lemma size_aperySet (gens : List ℕ) (m : ℕ) : (aperySet gens m).size = m := by
  simp only [aperySet]
  rw [size_iter, size_initA]

lemma relaxRound_sound (gens : List ℕ) (m : ℕ) (hm : 0 < m) (dist : Array (Option ℕ))
    (hsz : dist.size = m) (hS : Sound gens m dist) : Sound gens m (relaxRound gens m dist) :=
  foldl_res_sound gens m hm (List.range m) dist hsz hS

lemma sound_iter (gens : List ℕ) (m : ℕ) (hm : 0 < m) : ∀ (K : ℕ) (dist : Array (Option ℕ)),
    dist.size = m → Sound gens m dist →
      Sound gens m ((List.range K).foldl (fun acc _ => relaxRound gens m acc) dist) := by
  intro K
  induction K with
  | zero => intro dist _ hS; simpa using hS
  | succ K ih =>
      intro dist hsz hS
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      have h2 : ((List.range K).foldl (fun acc _ => relaxRound gens m acc) dist).size = m := by
        rw [size_iter, hsz]
      exact relaxRound_sound gens m hm _ h2 (ih dist hsz hS)

/-- **Soundness.**  Every entry the algorithm produces is a genuine semigroup
element lying in its own residue class. -/
theorem apery_sound (gens : List ℕ) (m : ℕ) (hm : 0 < m) : Sound gens m (aperySet gens m) := by
  simp only [aperySet]
  exact sound_iter gens m hm _ (initA m) (size_initA m) (initA_sound gens m hm)

/-- **Minimality.**  Nothing in the semigroup beats its table entry.  This is
where the `m-1` bound is used: `short_rep` supplies a representation short
enough for `m-1` rounds to have reached. -/
theorem apery_min (gens : List ℕ) (m : ℕ) (hm : 0 < m) (hpos : ∀ g ∈ gens, 0 < g)
    {n : ℕ} (hn : InSG gens n) : OLe (aperySet gens m)[n % m]! (some n) := by
  obtain ⟨l, hl, hlen, hsum, hmod⟩ := short_rep hm hpos hn
  have hC : Covers gens m (0 + (m - 1)) (aperySet gens m) :=
    covers_iter gens m hm (m - 1) (initA m) 0 (size_initA m) (initA_covers gens m hm)
  have hres := hC l hl (by omega)
  rw [hmod] at hres
  obtain ⟨a, ha, hab⟩ := hres
  exact ⟨a, ha, by omega⟩

lemma insg_inv {gens : List ℕ} {n : ℕ} (h : InSG gens n) (hn : n ≠ 0) :
    ∃ g ∈ gens, ∃ n2, n = g + n2 ∧ InSG gens n2 := by
  cases h with
  | zero => exact absurd rfl hn
  | @step g n2 hg hn2 => exact ⟨g, hg, n2, rfl, hn2⟩

/-! ## Reachability from coprimality

The reachable residues form a subset of `ZMod m` containing `0` and closed under
addition.  It is in fact a *subgroup*, for a cheap reason: `m • x = 0` in
`ZMod m`, so `-x = (m-1) • x`, and `(m-1) * n` is a semigroup element whenever
`n` is.  No finiteness or element-order argument is needed.

A subgroup absorbs integer multiples, and Bézout writes `gcd a b` as an integer
combination of `a` and `b`.  Folding along the generator list puts the gcd of
all generators into the subgroup; when that gcd is `1`, the subgroup contains
`1` and hence everything. -/

lemma insg_add {gens : List ℕ} {a b : ℕ} (ha : InSG gens a) (hb : InSG gens b) :
    InSG gens (a + b) := by
  induction ha with
  | zero => simpa using hb
  | @step g n hg hn ih =>
      have h := InSG.step hg ih
      rwa [← Nat.add_assoc] at h

lemma insg_nsmul {gens : List ℕ} {a : ℕ} (ha : InSG gens a) : ∀ c : ℕ, InSG gens (c * a) := by
  intro c
  induction c with
  | zero => simpa using InSG.zero
  | succ c ih =>
      have he : (c + 1) * a = a + c * a := by ring
      rw [he]
      exact insg_add ha ih

lemma insg_gen {gens : List ℕ} {g : ℕ} (hg : g ∈ gens) : InSG gens g := by
  simpa using InSG.step hg InSG.zero

/-- The residues reachable by the semigroup, as an additive subgroup of
`ZMod m`.  Closure under negation is the only interesting field. -/
def Him (gens : List ℕ) (m : ℕ) (hm : 0 < m) : AddSubgroup (ZMod m) where
  carrier := { x | ∃ n, InSG gens n ∧ (n : ZMod m) = x }
  zero_mem' := ⟨0, InSG.zero, by simp⟩
  add_mem' := by
    rintro x y ⟨n1, h1, rfl⟩ ⟨n2, h2, rfl⟩
    exact ⟨n1 + n2, insg_add h1 h2, by push_cast; ring⟩
  neg_mem' := by
    rintro x ⟨n, h, rfl⟩
    refine ⟨(m - 1) * n, insg_nsmul h _, ?_⟩
    have hc : ((m - 1 : ℕ) : ZMod m) = -1 := by
      rw [Nat.cast_sub hm, ZMod.natCast_self]
      simp
    push_cast [hc]
    ring

lemma gen_mem (gens : List ℕ) (m : ℕ) (hm : 0 < m) {g : ℕ} (hg : g ∈ gens) :
    ((g : ℕ) : ZMod m) ∈ Him gens m hm :=
  ⟨g, insg_gen hg, rfl⟩

/-- A subgroup containing `a` and `b` contains `gcd a b`, by Bézout. -/
lemma gcd_mem (gens : List ℕ) (m : ℕ) (hm : 0 < m) {a b : ℕ}
    (ha : ((a : ℕ) : ZMod m) ∈ Him gens m hm) (hb : ((b : ℕ) : ZMod m) ∈ Him gens m hm) :
    ((Nat.gcd a b : ℕ) : ZMod m) ∈ Him gens m hm := by
  have hbez : (Nat.gcd a b : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := Nat.gcd_eq_gcd_ab a b
  have hcast : ((Nat.gcd a b : ℕ) : ZMod m)
      = (Nat.gcdA a b) • ((a : ℕ) : ZMod m) + (Nat.gcdB a b) • ((b : ℕ) : ZMod m) := by
    have h2 := congrArg (fun z : ℤ => ((z : ℤ) : ZMod m)) hbez
    push_cast at h2
    rw [h2]
    simp [zsmul_eq_mul]
    ring
  rw [hcast]
  exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _ ha _) (AddSubgroup.zsmul_mem _ hb _)

lemma foldr_gcd_mem (gens : List ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ (l : List ℕ), (∀ x ∈ l, x ∈ gens) →
      ((l.foldr Nat.gcd 0 : ℕ) : ZMod m) ∈ Him gens m hm := by
  intro l
  induction l with
  | nil => intro _; simpa using (Him gens m hm).zero_mem
  | cons a t ih =>
      intro hl
      have ha : a ∈ gens := hl a (by simp)
      have ht : ∀ x ∈ t, x ∈ gens := fun x hx => hl x (by simp [hx])
      simp only [List.foldr_cons]
      exact gcd_mem gens m hm (gen_mem gens m hm ha) (ih ht)

/-- **Reachability from coprimality.**  If the generators are collectively
coprime then every residue class mod `m` contains a semigroup element. -/
theorem hsurj_of_gcd (gens : List ℕ) (m : ℕ) (hm : 0 < m)
    (hgcd : gens.foldr Nat.gcd 0 = 1) :
    ∀ r < m, ∃ n, InSG gens n ∧ n % m = r := by
  have h1 : ((1 : ℕ) : ZMod m) ∈ Him gens m hm := by
    rw [← hgcd]
    exact foldr_gcd_mem gens m hm gens (fun x hx => hx)
  intro r hr
  have hrmem : ((r : ℕ) : ZMod m) ∈ Him gens m hm := by
    have he : ((r : ℕ) : ZMod m) = r • ((1 : ℕ) : ZMod m) := by push_cast; simp
    rw [he]
    exact AddSubgroup.nsmul_mem _ h1 r
  obtain ⟨n, hn, hcast⟩ := hrmem
  refine ⟨n, hn, ?_⟩
  have hmod : n % m = r % m := (ZMod.natCast_eq_natCast_iff n r m).mp hcast
  rw [hmod, Nat.mod_eq_of_lt hr]

/-! ## The certificate always holds -/

def aperyW (gens : List ℕ) (m : ℕ) (r : ℕ) : ℕ := ((aperySet gens m)[r]!).getD 0

variable {gens : List ℕ} {m : ℕ}

lemma aperyW_of (h : (aperySet gens m)[r]! = some v) : aperyW gens m r = v := by
  simp only [aperyW, h, Option.getD]

/-- Every entry is a genuine semigroup element sitting in its own class. -/
lemma aperyW_spec (hm : 0 < m) (hpos : ∀ g ∈ gens, 0 < g)
    (hsurj : ∀ r < m, ∃ n, InSG gens n ∧ n % m = r) (r : ℕ) (hr : r < m) :
    InSG gens (aperyW gens m r) ∧ aperyW gens m r % m = r := by
  obtain ⟨n, hn, hnr⟩ := hsurj r hr
  obtain ⟨a, ha, hab⟩ := apery_min gens m hm hpos hn
  rw [hnr] at ha
  obtain ⟨hsg, hmod⟩ := apery_sound gens m hm r a ha
  rw [aperyW_of ha]
  exact ⟨hsg, by rw [hmod, Nat.mod_eq_of_lt hr]⟩

/-- Nothing in the semigroup beats its entry, stated for `aperyW`. -/
lemma aperyW_le (hm : 0 < m) (hpos : ∀ g ∈ gens, 0 < g) {n : ℕ} (hn : InSG gens n) :
    aperyW gens m (n % m) ≤ n := by
  obtain ⟨a, ha, hab⟩ := apery_min gens m hm hpos hn
  rw [aperyW_of ha]
  exact hab

/-- **The algorithm always produces a certified table.**

No check is required: `CertCheck` cannot fail on an admissible input. -/
theorem apery_cert (hm : 0 < m) (hmg : m ∈ gens) (hpos : ∀ g ∈ gens, 0 < g)
    (hsurj : ∀ r < m, ∃ n, InSG gens n ∧ n % m = r) :
    AperyCert gens m (aperyW gens m) := by
  refine ⟨hm, hmg, hpos, ?_, ?_, ?_, ?_⟩
  · -- wzero
    obtain ⟨a, ha, hab⟩ := apery_min gens m hm hpos (InSG.zero (gens := gens))
    rw [Nat.zero_mod] at ha
    rw [aperyW_of ha]
    omega
  · -- wmod
    intro r hr
    exact (aperyW_spec hm hpos hsurj r hr).2
  · -- closed
    intro r hr g hg
    have hw := (aperyW_spec hm hpos hsurj r hr).1
    have hsum : InSG gens (aperyW gens m r + g) := by
      have := InSG.step hg hw
      rwa [Nat.add_comm] at this
    exact aperyW_le hm hpos hsum
  · -- pred
    intro r hr hr0
    obtain ⟨hwSG, hwmod⟩ := aperyW_spec hm hpos hsurj r hr
    have hwne : aperyW gens m r ≠ 0 := by
      intro h; rw [h] at hwmod; simp at hwmod; omega
    obtain ⟨g, hg, n2, hn2eq, hn2⟩ := insg_inv hwSG hwne
    refine ⟨g, hg, by omega, ?_⟩
    have hsub : aperyW gens m r - g = n2 := by omega
    rw [hsub]
    -- Show `w (n2 % m) = n2`.  It is at most `n2`; if it were strictly less,
    -- adding `g` back would give a smaller element of class `r` than `w r`.
    have hle : aperyW gens m (n2 % m) ≤ n2 := aperyW_le hm hpos hn2
    by_contra hne
    have hlt : aperyW gens m (n2 % m) < n2 := by omega
    have hrlt : n2 % m < m := Nat.mod_lt _ hm
    obtain ⟨haSG, hamod⟩ := aperyW_spec hm hpos hsurj (n2 % m) hrlt
    have hstep : InSG gens (aperyW gens m (n2 % m) + g) := by
      have := InSG.step hg haSG
      rwa [Nat.add_comm] at this
    have hres : (aperyW gens m (n2 % m) + g) % m = r := by
      rw [Nat.add_mod, hamod, ← Nat.add_mod, Nat.add_comm n2 g, ← hn2eq, hwmod]
    have hkey := aperyW_le hm hpos hstep
    rw [hres] at hkey
    omega

/-! ## Bridge to the executable definition in `Basic.lean`

`aperySet` at the root is the function the program actually runs.  The `rfl`
below says it is the *same term* as the one reasoned about above -- not merely
equal on every input, but definitionally identical.  Without it this file would
only describe a lookalike. -/

theorem aperySet_eq : @_root_.NumSemigroups.aperySet = @aperySet := rfl

/-! ## Final form: no hypotheses left to discharge

Every remaining assumption is elementary and decidable on a concrete input. -/

/-- **The algorithm is correct whenever the generators are coprime.** -/
theorem apery_cert_of_gcd {gens : List ℕ} {m : ℕ} (hm : 0 < m) (hmg : m ∈ gens)
    (hpos : ∀ g ∈ gens, 0 < g) (hgcd : gens.foldr Nat.gcd 0 = 1) :
    AperyCert gens m (aperyW gens m) :=
  apery_cert hm hmg hpos (hsurj_of_gcd gens m hm hgcd)

/-- **Unconditional correctness of the algorithm in `Basic.lean`.**

For any list of positive generators with gcd 1, `m` one of them, the table the
program computes satisfies the certificate.  No check is required, and nothing
is assumed about the algorithm. -/
theorem basic_apery_cert {gens : List ℕ} {m : ℕ} (hm : 0 < m) (hmg : m ∈ gens)
    (hpos : ∀ g ∈ gens, 0 < g) (hgcd : gens.foldr Nat.gcd 0 = 1) :
    AperyCert gens m (fun r => ((_root_.NumSemigroups.aperySet gens m)[r]!).getD 0) := by
  rw [aperySet_eq]
  exact apery_cert_of_gcd hm hmg hpos hgcd

end Complete

end NumSemigroups
