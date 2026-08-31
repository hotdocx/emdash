/* Reviewer-facing finite vector/matrix presentation consumer. */

require open emdash.emdash3_2_commutative_algebra_finite_modules;

symbol finite_module_vector_example
  (R : τ CommRing)
  (a b : τ (@comm_ring_carrier R))
  : τ (@CommRingVector R (succ (succ zero)))
≔ @finite_family_pair (@comm_ring_carrier R) a b;

symbol finite_module_matrix_example
  (R : τ CommRing)
  (a b c d : τ (@comm_ring_carrier R))
  : τ (@CommRingMatrix R
      (succ (succ zero))
      (succ (succ zero)))
≔ @finite_family_pair
    (@CommRingVector R (succ (succ zero)))
    (@finite_module_vector_example R a b)
    (@finite_module_vector_example R c d);

// Visible matrix action is the linear combination of its two columns.
assert
  (R : τ CommRing)
  (a b c d x y : τ (@comm_ring_carrier R))
  ⊢ @comm_ring_matrix_apply R
      (succ (succ zero))
      (succ (succ zero))
      (@finite_module_matrix_example R a b c d)
      (@finite_module_vector_example R x y)
  ≡ @comm_ring_vector_add R (succ (succ zero))
      (@comm_ring_vector_scale R (succ (succ zero))
        x (@finite_module_vector_example R a b))
      (@comm_ring_vector_add R (succ (succ zero))
        (@comm_ring_vector_scale R (succ (succ zero))
          y (@finite_module_vector_example R c d))
        (@comm_ring_vector_zero R (succ (succ zero))));

// Presentation agreement is explicit coefficient/equation data.
symbol finite_module_agreement_example
  (R : τ CommRing)
  (A : τ (@CommRingMatrix R (succ zero) (succ zero)))
  (v w : τ (@CommRingVector R (succ zero)))
  (c : τ (@CommRingVector R (succ zero)))
  (law : τ (@= (@CommRingVector R (succ zero))
      (@comm_ring_matrix_apply R (succ zero) (succ zero) A c)
      (@comm_ring_vector_sub R (succ zero) v w)))
  : τ (@CommRingPresentationAgreement
      R (succ zero) (succ zero) A v w)
≔ @comm_ring_presentation_agreement_intro R
    (succ zero) (succ zero) A v w c law;

// A nonzero-column matrix remains distinct from the zero-matrix presentation.
assertnot
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  ⊢ @finite_family_singleton
      (@CommRingVector R (succ zero))
      (@finite_family_singleton (@comm_ring_carrier R) a)
  ≡ @comm_ring_matrix_zero R (succ zero) (succ zero);
