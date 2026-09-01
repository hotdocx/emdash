/*
  Uniqueness of matrices with zero target rows.

  This shape lemma belongs below both finite-free and Freyd terminal-object
  constructions. It is recursive finite-family uniqueness, not a categorical
  terminality assertion or a second zero-matrix operation.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_block_laws;

// Every zero-row matrix is the selected zero matrix.
symbol comm_ring_matrix_zero_rows_path
  (R : τ CommRing)
  (columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R zero columns))
  : τ (@= (@CommRingMatrix R zero columns)
      A (@comm_ring_matrix_zero R zero columns))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R zero columns0) (λ A0 : τ _,
        @= (@CommRingMatrix R zero columns0)
          A0 (@comm_ring_matrix_zero R zero columns0)))
    (λ A0 : τ (@CommRingMatrix R zero zero),
      @eq_sym Unit_grpd
        (@is_contr_center Unit_grpd unit_is_contr) A0
        (@is_contr_path Unit_grpd unit_is_contr A0))
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ A0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R zero) columns0
        A0 (@comm_ring_matrix_zero R zero (succ columns0))
        (@eq_sym Unit_grpd
          (@is_contr_center Unit_grpd unit_is_contr)
          (@finite_family_head (@CommRingVector R zero) columns0 A0)
          (@is_contr_path Unit_grpd unit_is_contr
            (@finite_family_head (@CommRingVector R zero) columns0 A0)))
        (ih (@finite_family_tail
          (@CommRingVector R zero) columns0 A0)))
    columns) A;
