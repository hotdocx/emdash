require open emdash.emdash3_2_commutative_algebra_freyd_native_input_comparisons;
symbol R : τ CommRing;
symbol M : τ (FreydHomologyModel R);
symbol A : τ (@CommRingPresentation R);
symbol B : τ (@CommRingPresentation R);
symbol D : τ (@CommRingPresentation R);
symbol e : τ (@CommRingPresentationMorphism R A B);
symbol d : τ (@CommRingPresentationMorphism R B D);
symbol chain : τ (@CommRingFreydChainPair R A B D e d);

symbol original_input ≔ @freyd_homology_model_input R M A B D e d chain;
symbol native_input ≔ @freyd_raw_chain_native_cone R A B D e d chain;
symbol comparison ≔ @freyd_homology_model_native_input_map R M A B D e d chain;
symbol comparison_equiv ≔ @freyd_homology_model_native_input_equiv R M A B D e d chain;
symbol original_H ≔ @freyd_homology_model_object R M A B D e d chain;
symbol native_H ≔ @fapp0 _ _ (@freyd_homology_model_func R M) native_input;
symbol Hcomparison ≔ @freyd_homology_model_native_homology_map R M A B D e d chain;
symbol Hcomparison_equiv ≔ @freyd_homology_model_native_homology_equiv R M A B D e d chain;

// Both actual input endpoints and the actual comparison are retained.
assert ⊢ comparison_equiv : τ (@OmegaEquivAlong
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)) original_input native_input comparison);
assert ⊢ sigma_Fst comparison ≡ @id (@CommRingFreydPresentation_cat R) A;
assert ⊢ sigma_Fst (sigma_Snd comparison) ≡ @id (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@chain_pair_outgoing_diagram (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain));

// The comparison at H is exactly the existing whole functor's action.
assert ⊢ Hcomparison ≡ @fapp1_fapp0 _ _ (@freyd_homology_model_func R M)
  original_input native_input comparison;
assert ⊢ Hcomparison_equiv : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R)
  original_H native_H Hcomparison);

// The selected inverse is mapped, not reselected.
assert ⊢ @omega_equiv_along_left_inv (@CommRingFreydPresentation_cat R)
  original_H native_H Hcomparison Hcomparison_equiv
  ≡ @fapp1_fapp0 _ _ (@freyd_homology_model_func R M) native_input original_input
    (@omega_equiv_along_left_inv (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      original_input native_input comparison comparison_equiv);

// A complete Hom functor remains at the same two H objects.
assert ⊢ @fapp1_func _ _ (@freyd_homology_model_func R M) original_input native_input
  : τ (Functor (Hom_cat (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) original_input native_input)
    (Hom_cat (@CommRingFreydPresentation_cat R) original_H native_H));
