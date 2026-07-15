/-- Fuel-bounded helper: can n be written as a sum of elements from gens
(repeats allowed)? fuel is just an upper bound so Lean can see this
terminates; it always resolves via the n == 0 case before fuel runs out. -/
def canMakeAux (gens : List Nat) : Nat → Nat → Bool
  | 0, n => n == 0
  | fuel + 1, n =>
    if n == 0 then
      true
    else
      gens.any (fun g => g ≠ 0 && g ≤ n && canMakeAux gens fuel (n - g))

/-- Can n be paid using coins with values in gens? -/
def canMake (gens : List Nat) (n : Nat) : Bool :=
  canMakeAux gens n n

/-- Brute-force Frobenius number: the largest gap up to bound.
(If nothing up to bound is a gap, returns 0 — raise bound if that happens.) -/
def frobeniusUpTo (gens : List Nat) (bound : Nat) : Nat :=
  ((List.range (bound + 1)).filter (fun n => !canMake gens n)).foldr Nat.max 0

theorem frobenius_3_5_7 : frobeniusUpTo [3, 5, 7] 20 = 4 := by
  native_decide

#print axioms frobenius_3_5_7

theorem frobenius_3_5_7_decide : frobeniusUpTo [3, 5, 7] 20 = 4 := by
  decide

#print axioms frobenius_3_5_7_decide
