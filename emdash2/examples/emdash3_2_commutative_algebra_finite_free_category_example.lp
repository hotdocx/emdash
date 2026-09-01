/* Reviewer-facing finite-free matrix-category consumer. */

require open emdash.emdash3_2_commutative_algebra_finite_free_category;

assert
  (R : τ CommRing)
  ⊢ Obj (@CommRingFiniteFree_cat R)
  ≡ Nat_grpd;

assert
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  ⊢ Hom_cat (@CommRingFiniteFree_cat R) source target
  ≡ Path_cat (@CommRingMatrix R target source);

assert
  (R : τ CommRing)
  ⊢ @comm_ring_finite_free_id_matrix R zero
  ≡ @finite_family_nil (@CommRingVector R zero);

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  ⊢ @finite_family_head
      (@CommRingVector R (succ n)) n
      (@comm_ring_finite_free_id_matrix R (succ n))
  ≡ @finite_family_cons
      (@comm_ring_carrier R) n
      (@comm_ring_one R)
      (@comm_ring_vector_zero R n);

assert
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle (succ source)))
  ⊢ @finite_family_head
      (@CommRingVector R target) source
      (@comm_ring_finite_free_comp_matrix
        R (succ source) middle target g f)
  ≡ @comm_ring_matrix_apply R target middle g
      (@finite_family_head (@CommRingVector R middle) source f);

assertnot
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (A : τ (@CommRingMatrix R n n))
  ⊢ @comm_ring_finite_free_id_matrix R n
  ≡ A;
