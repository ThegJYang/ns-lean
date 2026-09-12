import NumSemigroups.PaperClaims

/-  Axiom audit.

    Not part of the library: nothing imports this, and it lives outside
    NumSemigroups/, so `lake build` ignores it.  Run it directly with

      lake env lean audit.lean

    It imports the already-compiled PaperClaims.olean, so it costs seconds
    rather than re-elaborating every `decide`.

    Every line should read [propext, Classical.choice, Quot.sound].
    Anything containing `sorryAx` is a theorem that silently failed.
    Anything containing `native_decide` is one of the six known exceptions.  -/

#print axioms fib_case1a_i5_k5
#print axioms fib_case1a_i3_k6
#print axioms fib_case1b_i5_k3
#print axioms fib_case1b_i7_k6
#print axioms fib_case2_i11_k6
#print axioms fib_genus_i5_k3
#print axioms thabit_n0
#print axioms thabit_kEqn
#print axioms thabit_kEqnMinus1
#print axioms thabit_kLtN_ex1
#print axioms thabit_kLtN_ex2
#print axioms thabit_kGtN
#print axioms grepunit_thm35
#print axioms grepunit_thm35_genus
#print axioms grepunit_thm41
#print axioms grepunit_thm41_genus
#print axioms grepunit_cor42_frobenius
#print axioms grepunit_cor42_genus_TRUE
#print axioms linrec_cor51
#print axioms linrec_ex52_2_n1_TRUE
#print axioms linrec_ex52_2_n2_TRUE
#print axioms linrec_ex62_genus
#print axioms linrec_pow2_kGt
#print axioms linrec_k1_n1
#print axioms linrec_k1_nGt1
#print axioms linrec_n1_kSmall
#print axioms linrec_n1_kLarge
#print axioms linrec_nGt1_kSmall_NOFORMULA
#print axioms geom_k1
#print axioms geom_k2
#print axioms geom_k3
#print axioms geom_k2_alt
#print axioms geom_swap
#print axioms tri_odd_n3
#print axioms tri_even_n4
#print axioms tet_n0mod6
#print axioms tet_n1mod6
#print axioms tet_n2mod6
#print axioms tet_n3mod6
#print axioms tet_n4mod6
#print axioms tet_n5mod6
#print axioms sqfib_case1_n6
#print axioms sqfib_case2_n5
#print axioms sqfib_case3_n4
#print axioms sqfib_degenerate_n3
#print axioms song_thabit_b3n1
#print axioms song_thabit_b2n1
#print axioms song_thabit_b2n2
#print axioms song_thabit_b3n1_genus_TRUE
#print axioms song_thabit_n0_TRUE
#print axioms song_2nd_b3n0
#print axioms song_2nd_b2n1
#print axioms song_2nd_b2n1_genus
#print axioms song_2nd_b2n2_TRUE
#print axioms song_2nd_b2n2_genus
#print axioms song_cunn_b10n0
#print axioms song_cunn_b2n1
#print axioms song_cunn_b2n2
#print axioms song_cunn_b2n3
#print axioms song_fermat_b2n0
#print axioms song_fermat_b2n1
#print axioms song_fermat_b2n2
#print axioms song_fermat_b2n0_genus
