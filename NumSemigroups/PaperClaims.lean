import NumSemigroups.Basic

/- Audit target: arXiv:math/0606717, "On the Frobenius Number of
Fibonacci Numerical Semigroups" (Marín, Ramírez Alfonsín, Revuelta).
Theorem 1.1 gives g(Fi, F{i+2}, F_{i+k}) in closed form.
Testing the case i = 5, k = 3: generators are F5=5, F7=13, F8=21;
the paper's formula predicts a Frobenius number of 37. -/

theorem paper_0606717_i5_k3 :
    frobeniusNumber [5, 13, 21] = 37 := by
  native_decide

#print axioms paper_0606717_i5_k3

/- Now that distinctPrimeFactorsAux/constructCoprimePartner are
fuel-based (no longer partial), frobeniusNumber's whole bound-search
is kernel-reducible again, so this can go back to a plain `decide` —
zero extra axioms, no fallback to native_decide needed. -/
set_option maxRecDepth 4000 in
theorem paper_0606717_i5_k3_decide :
    frobeniusNumber [5, 13, 21] = 37 := by
  decide

#print axioms paper_0606717_i5_k3_decide

theorem paper_0606717_i3_k3 :
    frobeniusNumber [2, 5, 8] = 3 := by
  native_decide

theorem paper_0606717_i4_k3 :
    frobeniusNumber [3, 8, 13] = 10 := by
  native_decide

theorem paper_0606717_i5_k4 :
    frobeniusNumber [5, 13, 34] = 42 := by
  native_decide

theorem paper_0606717_i6_k4 :
    frobeniusNumber [8, 21, 55] = 123 := by
  native_decide

theorem paper_0606717_i7_k4 :
    frobeniusNumber [13, 34, 89] = 343 := by
  native_decide

/- Previously flagged in results-table.md as untestable: the "otherwise"
branch of Theorem 1.1, i = 11, k = 6. Generators F11, F13, F17 = 89, 233,
1597; the paper predicts Frobenius number 17512. With the DP-based core
this is now tractable. -/
theorem paper_0606717_otherwise_i11_k6 :
    frobeniusNumber [89, 233, 1597] = 17512 := by
  native_decide

#print axioms paper_0606717_otherwise_i11_k6

/- Audit target: arXiv:1510.04801, "The Frobenius problem for generalized
Thabit numerical semigroups" (Kyunghwan Song). GT(n,k) is the generalized
Thabit semigroup with generators s_i = (2^k+1)*2^(n+i) - (2^k-1). The paper
splits F(GT(n,k)) into cases on how k relates to n. -/

/- Case n = 0 (Lemma 4.9): F(GT(0,k)) = 2^k + 1.
   GT(0,3) = <2,11> (Example 3.8). -/
theorem paper_1510_04801_n0 :
    frobeniusNumber [2, 11] = 9 := by
  native_decide

#print axioms paper_1510_04801_n0

/- Case k = n ≥ 1 (Lemma 4.10): F(GT(n,n)) = (2^n+1)*2^n*(2^(2n)+1) - (2^n-1).
   GT(2,2) generators from Theorem 3.6; F hand-derived from the closed form,
   not directly quoted from the paper's own worked examples. -/
theorem paper_1510_04801_kEqn :
    frobeniusNumber [17, 37, 77, 157, 317] = 337 := by
  native_decide

#print axioms paper_1510_04801_kEqn

/- Case k = n - 1 (Corollary 4.12): F(GT(n,n-1)) closed form.
   GT(3,2) = <37,77,157,317,637,1277> (Example 3.9 generators);
   F hand-derived from the closed form. -/
theorem paper_1510_04801_kEqnMinus1 :
    frobeniusNumber [37, 77, 157, 317, 637, 1277] = 1551 := by
  native_decide

#print axioms paper_1510_04801_kEqnMinus1

/- Case 2 ≤ k < n, general (§4.2, Example 4.14/4.18). -/
theorem paper_1510_04801_kLtN_ex1 :
    frobeniusNumber [281, 569, 1145, 2297, 4601, 9209, 18425, 36857, 73721] = 81483 := by
  native_decide

#print axioms paper_1510_04801_kLtN_ex1

/- Case 2 ≤ k < n, general (§4.2, Example 4.19). -/
theorem paper_1510_04801_kLtN_ex2 :
    frobeniusNumber [1145, 2297, 4601, 9209, 18425, 36857, 73721, 147449, 294905, 589817, 1179641] = 1325903 := by
  native_decide

#print axioms paper_1510_04801_kLtN_ex2

/- Case n ≠ 0, k > n, k ≠ 2 (§4.3, Example 4.26). Intermediate step (t2=2)
   is quoted from the paper; the final subtraction to 1095 I completed
   by hand since the source text cut off before stating it. -/
theorem paper_1510_04801_kGtN :
    frobeniusNumber [29, 65, 137, 281, 569] = 1095 := by
  native_decide

#print axioms paper_1510_04801_kGtN

/- TODO: the paper's genuine exception case (n,k) = (1,2), GT(1,2) = <7,17,37>.
   Not included — I couldn't retrieve the paper's resolution of this case. -/
