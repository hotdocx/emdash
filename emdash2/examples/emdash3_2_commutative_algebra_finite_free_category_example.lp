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

// The rigid categorical representation agrees with the transparent evaluator
// by a constructed recursive path, not by a runtime fold or opaque bridge.
symbol finite_free_rigid_transparent_reviewer_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_finite_free_comp_matrix
        R source middle target g f)
      (@comm_ring_matrix_comp R target middle source g f))
≔ @comm_ring_finite_free_comp_transparent_path
    R source middle target g f;

// The generic category operation reaches the same evaluator propositionally
// through its proof-time rigid-head usability comparison.
symbol finite_free_generic_transparent_reviewer_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0
        (@CommRingFiniteFree_cat R)
        source middle target g f)
      (@comm_ring_matrix_comp R target middle source g f))
≔ @comm_ring_finite_free_comp_fapp0_transparent_path
    R source middle target g f;

symbol finite_free_matrix_right_identity_reviewer_path
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_matrix_comp R target source source g
        (@comm_ring_finite_free_id_matrix R source))
      g)
≔ @comm_ring_matrix_comp_right_identity_path R source target g;

symbol finite_free_matrix_left_identity_reviewer_path
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_matrix_comp R target target source
        (@comm_ring_finite_free_id_matrix R target) g)
      g)
≔ @comm_ring_matrix_comp_left_identity_path R source target g;

symbol finite_free_matrix_assoc_reviewer_path
  (R : τ CommRing)
  (A B C D : τ Nat_grpd)
  (h : τ (@CommRingMatrix R D C))
  (g : τ (@CommRingMatrix R C B))
  (f : τ (@CommRingMatrix R B A))
  : τ (@= (@CommRingMatrix R D A)
      (@comm_ring_matrix_comp R D C A h
        (@comm_ring_matrix_comp R C B A g f))
      (@comm_ring_matrix_comp R D B A
        (@comm_ring_matrix_comp R D C B h g) f))
≔ @comm_ring_matrix_comp_assoc_path R A B C D h g f;

assertnot
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (A : τ (@CommRingMatrix R n n))
  ⊢ @comm_ring_finite_free_id_matrix R n
  ≡ A;
