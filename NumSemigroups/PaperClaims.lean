import NumSemigroups.Basic

/- Audit target: arXiv:math/0606717, "On the Frobenius Number of
Fibonacci Numerical Semigroups" (Marín, Ramírez Alfonsín, Revuelta).
Theorem 1.1 gives g(Fi, F{i+2}, F_{i+k}) in closed form.
Testing the case i = 5, k = 3: generators are F5=5, F7=13, F8=21;
the paper's formula predicts a Frobenius number of 37. -/

theorem paper_0606717_i5_k3 :
    frobeniusUpTo [5, 13, 21] 40 = 37 := by
  native_decide

#print axioms paper_0606717_i5_k3

theorem paper_0606717_i5_k3_decide :
    frobeniusUpTo [5, 13, 21] 40 = 37 := by
  decide

#print axioms paper_0606717_i5_k3_decide