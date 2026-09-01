/*
  Subtractive and congruence laws for finite column matrices.

  Inverse uniqueness is derived from the checked matrix additive-group paths.
  It yields involutive negation, negation of sums and subtraction, subtraction
  chaining/additivity, and compatibility of negation/subtraction with both
  sides of matrix composition. This module is rule-free and introduces no
  opaque equality witness.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_additive_laws;

symbol comm_ring_matrix_add_inv_left_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_neg R rows columns A) A)
      (@comm_ring_matrix_zero R rows columns))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_add_comm_path R rows columns
      (@comm_ring_matrix_neg R rows columns A) A)
    (@comm_ring_matrix_add_inv_path R rows columns A);

symbol comm_ring_matrix_add_inverse_unique_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  (law : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns A B)
      (@comm_ring_matrix_zero R rows columns)))
  : τ (@= (@CommRingMatrix R rows columns)
      B (@comm_ring_matrix_neg R rows columns A))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    B
    (@comm_ring_matrix_add R rows columns
      (@comm_ring_matrix_zero R rows columns) B)
    (@comm_ring_matrix_neg R rows columns A)
    (@eq_sym
      (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_zero R rows columns) B)
      B
      (@comm_ring_matrix_add_zero_left_path R rows columns B))
    (@eq_trans
      (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_zero R rows columns) B)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_neg R rows columns A) A) B)
      (@comm_ring_matrix_neg R rows columns A)
      (@eq_ap
        (@CommRingMatrix R rows columns)
        (@CommRingMatrix R rows columns)
        (λ X : τ (@CommRingMatrix R rows columns),
          @comm_ring_matrix_add R rows columns X B)
        (@comm_ring_matrix_zero R rows columns)
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_neg R rows columns A) A)
        (@eq_sym
          (@CommRingMatrix R rows columns)
          (@comm_ring_matrix_add R rows columns
            (@comm_ring_matrix_neg R rows columns A) A)
          (@comm_ring_matrix_zero R rows columns)
          (@comm_ring_matrix_add_inv_left_path R rows columns A)))
      (@eq_trans
        (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_add R rows columns
            (@comm_ring_matrix_neg R rows columns A) A) B)
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_neg R rows columns A)
          (@comm_ring_matrix_add R rows columns A B))
        (@comm_ring_matrix_neg R rows columns A)
        (@comm_ring_matrix_add_assoc_path R rows columns
          (@comm_ring_matrix_neg R rows columns A) A B)
        (@eq_trans
          (@CommRingMatrix R rows columns)
          (@comm_ring_matrix_add R rows columns
            (@comm_ring_matrix_neg R rows columns A)
            (@comm_ring_matrix_add R rows columns A B))
          (@comm_ring_matrix_add R rows columns
            (@comm_ring_matrix_neg R rows columns A)
            (@comm_ring_matrix_zero R rows columns))
          (@comm_ring_matrix_neg R rows columns A)
          (@eq_ap
            (@CommRingMatrix R rows columns)
            (@CommRingMatrix R rows columns)
            (λ X : τ (@CommRingMatrix R rows columns),
              @comm_ring_matrix_add R rows columns
                (@comm_ring_matrix_neg R rows columns A) X)
            (@comm_ring_matrix_add R rows columns A B)
            (@comm_ring_matrix_zero R rows columns)
            law)
          (@comm_ring_matrix_add_zero_right_path R rows columns
            (@comm_ring_matrix_neg R rows columns A)))));

symbol comm_ring_matrix_neg_involutive_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_neg R rows columns A))
      A)
≔ @eq_sym
    (@CommRingMatrix R rows columns)
    A
    (@comm_ring_matrix_neg R rows columns
      (@comm_ring_matrix_neg R rows columns A))
    (@comm_ring_matrix_add_inverse_unique_path R rows columns
      (@comm_ring_matrix_neg R rows columns A) A
      (@comm_ring_matrix_add_inv_left_path R rows columns A));

symbol comm_ring_matrix_neg_zero_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_zero R rows columns))
      (@comm_ring_matrix_zero R rows columns))
≔ @eq_sym
    (@CommRingMatrix R rows columns)
    (@comm_ring_matrix_zero R rows columns)
    (@comm_ring_matrix_neg R rows columns
      (@comm_ring_matrix_zero R rows columns))
    (@comm_ring_matrix_add_inverse_unique_path R rows columns
      (@comm_ring_matrix_zero R rows columns)
      (@comm_ring_matrix_zero R rows columns)
      (@comm_ring_matrix_add_zero_right_path R rows columns
        (@comm_ring_matrix_zero R rows columns)));

symbol comm_ring_matrix_add_interchange_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B C D : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_add R rows columns A B)
        (@comm_ring_matrix_add R rows columns C D))
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_add R rows columns A C)
        (@comm_ring_matrix_add R rows columns B D)))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_add_assoc_path R rows columns
      A B (@comm_ring_matrix_add R rows columns C D))
    (@eq_trans
      (@CommRingMatrix R rows columns)
      _ _ _
      (@eq_ap
        (@CommRingMatrix R rows columns)
        (@CommRingMatrix R rows columns)
        (λ X : τ (@CommRingMatrix R rows columns),
          @comm_ring_matrix_add R rows columns A X)
        (@comm_ring_matrix_add R rows columns B
          (@comm_ring_matrix_add R rows columns C D))
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_add R rows columns B C) D)
        (@eq_sym
          (@CommRingMatrix R rows columns)
          (@comm_ring_matrix_add R rows columns
            (@comm_ring_matrix_add R rows columns B C) D)
          (@comm_ring_matrix_add R rows columns B
            (@comm_ring_matrix_add R rows columns C D))
          (@comm_ring_matrix_add_assoc_path R rows columns B C D)))
      (@eq_trans
        (@CommRingMatrix R rows columns)
        _ _ _
        (@eq_ap
          (@CommRingMatrix R rows columns)
          (@CommRingMatrix R rows columns)
          (λ X : τ (@CommRingMatrix R rows columns),
            @comm_ring_matrix_add R rows columns A
              (@comm_ring_matrix_add R rows columns X D))
          (@comm_ring_matrix_add R rows columns B C)
          (@comm_ring_matrix_add R rows columns C B)
          (@comm_ring_matrix_add_comm_path R rows columns B C))
        (@eq_trans
          (@CommRingMatrix R rows columns)
          _ _ _
          (@eq_ap
            (@CommRingMatrix R rows columns)
            (@CommRingMatrix R rows columns)
            (λ X : τ (@CommRingMatrix R rows columns),
              @comm_ring_matrix_add R rows columns A X)
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_add R rows columns C B) D)
            (@comm_ring_matrix_add R rows columns C
              (@comm_ring_matrix_add R rows columns B D))
            (@comm_ring_matrix_add_assoc_path R rows columns C B D))
          (@eq_sym
            (@CommRingMatrix R rows columns)
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_add R rows columns A C)
              (@comm_ring_matrix_add R rows columns B D))
            (@comm_ring_matrix_add R rows columns A
              (@comm_ring_matrix_add R rows columns C
                (@comm_ring_matrix_add R rows columns B D)))
            (@comm_ring_matrix_add_assoc_path R rows columns
              A C (@comm_ring_matrix_add R rows columns B D))))));

symbol comm_ring_matrix_neg_add_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_add R rows columns A B))
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_neg R rows columns A)
        (@comm_ring_matrix_neg R rows columns B)))
≔ @eq_sym
    (@CommRingMatrix R rows columns)
    (@comm_ring_matrix_add R rows columns
      (@comm_ring_matrix_neg R rows columns A)
      (@comm_ring_matrix_neg R rows columns B))
    (@comm_ring_matrix_neg R rows columns
      (@comm_ring_matrix_add R rows columns A B))
    (@comm_ring_matrix_add_inverse_unique_path R rows columns
      (@comm_ring_matrix_add R rows columns A B)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_neg R rows columns A)
        (@comm_ring_matrix_neg R rows columns B))
      (@eq_trans
        (@CommRingMatrix R rows columns)
        _ _ _
        (@comm_ring_matrix_add_interchange_path
          R rows columns
          A B
          (@comm_ring_matrix_neg R rows columns A)
          (@comm_ring_matrix_neg R rows columns B))
        (@eq_trans
          (@CommRingMatrix R rows columns)
          _ _ _
          (@comm_ring_matrix_add_congr_path R rows columns
            (@comm_ring_matrix_add R rows columns A
              (@comm_ring_matrix_neg R rows columns A))
            (@comm_ring_matrix_zero R rows columns)
            (@comm_ring_matrix_add R rows columns B
              (@comm_ring_matrix_neg R rows columns B))
            (@comm_ring_matrix_zero R rows columns)
            (@comm_ring_matrix_add_inv_path R rows columns A)
            (@comm_ring_matrix_add_inv_path R rows columns B))
          (@comm_ring_matrix_add_zero_right_path R rows columns
            (@comm_ring_matrix_zero R rows columns)))));

symbol comm_ring_matrix_comp_neg_right_path
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (B : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns A
        (@comm_ring_matrix_neg R middle columns B))
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_comp R rows middle columns A B)))
≔ @comm_ring_matrix_add_inverse_unique_path R rows columns
    (@comm_ring_matrix_comp R rows middle columns A B)
    (@comm_ring_matrix_comp R rows middle columns A
      (@comm_ring_matrix_neg R middle columns B))
    (@eq_trans
      (@CommRingMatrix R rows columns)
      _ _ _
      (@eq_sym
        (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_comp R rows middle columns A
          (@comm_ring_matrix_add R middle columns B
            (@comm_ring_matrix_neg R middle columns B)))
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_comp R rows middle columns A B)
          (@comm_ring_matrix_comp R rows middle columns A
            (@comm_ring_matrix_neg R middle columns B)))
        (@comm_ring_matrix_comp_add_right_path R
          rows middle columns A B
          (@comm_ring_matrix_neg R middle columns B)))
      (@eq_trans
        (@CommRingMatrix R rows columns)
        _ _ _
        (@eq_ap
          (@CommRingMatrix R middle columns)
          (@CommRingMatrix R rows columns)
          (λ X : τ (@CommRingMatrix R middle columns),
            @comm_ring_matrix_comp R rows middle columns A X)
          (@comm_ring_matrix_add R middle columns B
            (@comm_ring_matrix_neg R middle columns B))
          (@comm_ring_matrix_zero R middle columns)
          (@comm_ring_matrix_add_inv_path R middle columns B))
        (@comm_ring_matrix_comp_zero_right_path R
          rows middle columns A)));

symbol comm_ring_matrix_comp_neg_left_path
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (B : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns
        (@comm_ring_matrix_neg R rows middle A) B)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_comp R rows middle columns A B)))
≔ @comm_ring_matrix_add_inverse_unique_path R rows columns
    (@comm_ring_matrix_comp R rows middle columns A B)
    (@comm_ring_matrix_comp R rows middle columns
      (@comm_ring_matrix_neg R rows middle A) B)
    (@eq_trans
      (@CommRingMatrix R rows columns)
      _ _ _
      (@eq_sym
        (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_comp R rows middle columns
          (@comm_ring_matrix_add R rows middle A
            (@comm_ring_matrix_neg R rows middle A)) B)
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_comp R rows middle columns A B)
          (@comm_ring_matrix_comp R rows middle columns
            (@comm_ring_matrix_neg R rows middle A) B))
        (@comm_ring_matrix_comp_add_left_path R
          rows middle columns A
          (@comm_ring_matrix_neg R rows middle A) B))
      (@eq_trans
        (@CommRingMatrix R rows columns)
        _ _ _
        (@eq_ap
          (@CommRingMatrix R rows middle)
          (@CommRingMatrix R rows columns)
          (λ X : τ (@CommRingMatrix R rows middle),
            @comm_ring_matrix_comp R rows middle columns X B)
          (@comm_ring_matrix_add R rows middle A
            (@comm_ring_matrix_neg R rows middle A))
          (@comm_ring_matrix_zero R rows middle)
          (@comm_ring_matrix_add_inv_path R rows middle A))
        (@comm_ring_matrix_comp_zero_left_path R
          rows middle columns B)));

symbol comm_ring_matrix_sub_refl_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_sub R rows columns A A)
      (@comm_ring_matrix_zero R rows columns))
≔ @comm_ring_matrix_add_inv_path R rows columns A;

symbol comm_ring_matrix_neg_sub_swap_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_sub R rows columns A B))
      (@comm_ring_matrix_sub R rows columns B A))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_neg_add_path R rows columns A
      (@comm_ring_matrix_neg R rows columns B))
    (@eq_trans
      (@CommRingMatrix R rows columns)
      _ _ _
      (@comm_ring_matrix_add_congr_path R rows columns
        (@comm_ring_matrix_neg R rows columns A)
        (@comm_ring_matrix_neg R rows columns A)
        (@comm_ring_matrix_neg R rows columns
          (@comm_ring_matrix_neg R rows columns B))
        B
        (@eq_refl (@CommRingMatrix R rows columns)
          (@comm_ring_matrix_neg R rows columns A))
        (@comm_ring_matrix_neg_involutive_path R rows columns B))
      (@comm_ring_matrix_add_comm_path R rows columns
        (@comm_ring_matrix_neg R rows columns A) B));

// Negating both endpoints reverses a subtraction.
symbol comm_ring_matrix_sub_neg_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_sub R rows columns
        (@comm_ring_matrix_neg R rows columns A)
        (@comm_ring_matrix_neg R rows columns B))
      (@comm_ring_matrix_sub R rows columns B A))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_add_congr_path R rows columns
      (@comm_ring_matrix_neg R rows columns A)
      (@comm_ring_matrix_neg R rows columns A)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_neg R rows columns B))
      B
      (@eq_refl (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_neg R rows columns A))
      (@comm_ring_matrix_neg_involutive_path R rows columns B))
    (@comm_ring_matrix_add_comm_path R rows columns
      (@comm_ring_matrix_neg R rows columns A) B);

symbol comm_ring_matrix_sub_chain_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B C : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_sub R rows columns A B)
        (@comm_ring_matrix_sub R rows columns B C))
      (@comm_ring_matrix_sub R rows columns A C))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_add_interchange_path R rows columns
      A (@comm_ring_matrix_neg R rows columns B)
      B (@comm_ring_matrix_neg R rows columns C))
    (@eq_trans
      (@CommRingMatrix R rows columns)
      _ _ _
      (@comm_ring_matrix_add_assoc_path R rows columns
        A B
        (@comm_ring_matrix_add R rows columns
          (@comm_ring_matrix_neg R rows columns B)
          (@comm_ring_matrix_neg R rows columns C)))
      (@eq_trans
        (@CommRingMatrix R rows columns)
        _ _ _
        (@eq_ap
          (@CommRingMatrix R rows columns)
          (@CommRingMatrix R rows columns)
          (λ X : τ (@CommRingMatrix R rows columns),
            @comm_ring_matrix_add R rows columns A X)
          (@comm_ring_matrix_add R rows columns B
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_neg R rows columns B)
              (@comm_ring_matrix_neg R rows columns C)))
          (@comm_ring_matrix_add R rows columns
            (@comm_ring_matrix_add R rows columns B
              (@comm_ring_matrix_neg R rows columns B))
            (@comm_ring_matrix_neg R rows columns C))
          (@eq_sym
            (@CommRingMatrix R rows columns)
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_add R rows columns B
                (@comm_ring_matrix_neg R rows columns B))
              (@comm_ring_matrix_neg R rows columns C))
            (@comm_ring_matrix_add R rows columns B
              (@comm_ring_matrix_add R rows columns
                (@comm_ring_matrix_neg R rows columns B)
                (@comm_ring_matrix_neg R rows columns C)))
            (@comm_ring_matrix_add_assoc_path R rows columns B
              (@comm_ring_matrix_neg R rows columns B)
              (@comm_ring_matrix_neg R rows columns C))))
        (@eq_trans
          (@CommRingMatrix R rows columns)
          _ _ _
          (@eq_ap
            (@CommRingMatrix R rows columns)
            (@CommRingMatrix R rows columns)
            (λ X : τ (@CommRingMatrix R rows columns),
              @comm_ring_matrix_add R rows columns A X)
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_add R rows columns B
                (@comm_ring_matrix_neg R rows columns B))
              (@comm_ring_matrix_neg R rows columns C))
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_zero R rows columns)
              (@comm_ring_matrix_neg R rows columns C))
            (@eq_ap
              (@CommRingMatrix R rows columns)
              (@CommRingMatrix R rows columns)
              (λ X : τ (@CommRingMatrix R rows columns),
                @comm_ring_matrix_add R rows columns X
                  (@comm_ring_matrix_neg R rows columns C))
              (@comm_ring_matrix_add R rows columns B
                (@comm_ring_matrix_neg R rows columns B))
              (@comm_ring_matrix_zero R rows columns)
              (@comm_ring_matrix_add_inv_path R rows columns B)))
          (@eq_ap
            (@CommRingMatrix R rows columns)
            (@CommRingMatrix R rows columns)
            (λ X : τ (@CommRingMatrix R rows columns),
              @comm_ring_matrix_add R rows columns A X)
            (@comm_ring_matrix_add R rows columns
              (@comm_ring_matrix_zero R rows columns)
              (@comm_ring_matrix_neg R rows columns C))
            (@comm_ring_matrix_neg R rows columns C)
            (@comm_ring_matrix_add_zero_left_path R rows columns
              (@comm_ring_matrix_neg R rows columns C))))));

symbol comm_ring_matrix_sub_add_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B A' B' : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_sub R rows columns
        (@comm_ring_matrix_add R rows columns A B)
        (@comm_ring_matrix_add R rows columns A' B'))
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_sub R rows columns A A')
        (@comm_ring_matrix_sub R rows columns B B')))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_add_congr_path R rows columns
      (@comm_ring_matrix_add R rows columns A B)
      (@comm_ring_matrix_add R rows columns A B)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_add R rows columns A' B'))
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_neg R rows columns A')
        (@comm_ring_matrix_neg R rows columns B'))
      (@eq_refl (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_add R rows columns A B))
      (@comm_ring_matrix_neg_add_path R rows columns A' B'))
    (@comm_ring_matrix_add_interchange_path R rows columns
      A B
      (@comm_ring_matrix_neg R rows columns A')
      (@comm_ring_matrix_neg R rows columns B'));

symbol comm_ring_matrix_comp_sub_right_path
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (B C : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns A
        (@comm_ring_matrix_sub R middle columns B C))
      (@comm_ring_matrix_sub R rows columns
        (@comm_ring_matrix_comp R rows middle columns A B)
        (@comm_ring_matrix_comp R rows middle columns A C)))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_comp_add_right_path R
      rows middle columns A B
      (@comm_ring_matrix_neg R middle columns C))
    (@comm_ring_matrix_add_congr_path R rows columns
      (@comm_ring_matrix_comp R rows middle columns A B)
      (@comm_ring_matrix_comp R rows middle columns A B)
      (@comm_ring_matrix_comp R rows middle columns A
        (@comm_ring_matrix_neg R middle columns C))
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_comp R rows middle columns A C))
      (@eq_refl (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_comp R rows middle columns A B))
      (@comm_ring_matrix_comp_neg_right_path R
        rows middle columns A C));

symbol comm_ring_matrix_comp_sub_left_path
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows middle))
  (C : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns
        (@comm_ring_matrix_sub R rows middle A B) C)
      (@comm_ring_matrix_sub R rows columns
        (@comm_ring_matrix_comp R rows middle columns A C)
        (@comm_ring_matrix_comp R rows middle columns B C)))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    _ _ _
    (@comm_ring_matrix_comp_add_left_path R
      rows middle columns A
      (@comm_ring_matrix_neg R rows middle B) C)
    (@comm_ring_matrix_add_congr_path R rows columns
      (@comm_ring_matrix_comp R rows middle columns A C)
      (@comm_ring_matrix_comp R rows middle columns A C)
      (@comm_ring_matrix_comp R rows middle columns
        (@comm_ring_matrix_neg R rows middle B) C)
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_comp R rows middle columns B C))
      (@eq_refl (@CommRingMatrix R rows columns)
        (@comm_ring_matrix_comp R rows middle columns A C))
      (@comm_ring_matrix_comp_neg_left_path R
        rows middle columns B C));
