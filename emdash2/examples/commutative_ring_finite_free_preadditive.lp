/* Reviewer-facing finite-free preadditive-category consumers. */

require open emdash.emdash3_2_commutative_algebra_finite_free_preadditive;

// Generic preadditive observations expose the existing matrix operations.
assert
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  ⊢ @preadditive_hom_zero
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_preadditive R)
      source target
  ≡ @comm_ring_matrix_zero R target source;

assert
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  (f g : τ (@CommRingMatrix R target source))
  ⊢ @preadditive_hom_add
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_preadditive R)
      source target f g
  ≡ @comm_ring_matrix_add R target source f g;

assert
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  (f : τ (@CommRingMatrix R target source))
  ⊢ @preadditive_hom_neg
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_preadditive R)
      source target f
  ≡ @comm_ring_matrix_neg R target source f;

// Both generic composition distributivity orientations are explicit paths.
assert
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f h : τ (@CommRingMatrix R middle source))
  ⊢ @comm_ring_finite_free_generic_comp_add_right_path
      R source middle target g f h
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target g
        (@comm_ring_matrix_add R middle source f h))
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g h)));

assert
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g h : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  ⊢ @comm_ring_finite_free_generic_comp_add_left_path
      R source middle target g h f
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target
        (@comm_ring_matrix_add R target middle g h) f)
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target h f)));
