/* Retained-model comparison with direct raw input, through actual categorical arrows. */
require open emdash.emdash3_2_one_cat_chain_pair_input_comparisons;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_adapter;
require open emdash.emdash3_2_commutative_algebra_freyd_native_inputs;

// The original raw fields determine the categorical input comparison internally.
symbol freyd_homology_model_native_input_map [R : τ CommRing]
  (M : τ (FreydHomologyModel R)) [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (Hom (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@freyd_homology_model_input R M A B D e d chain)
      (@freyd_raw_chain_native_cone R A B D e d chain))
≔ @chain_pair_retained_native_map (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
    (@freyd_homology_model_kernels R M) (@freyd_homology_model_kernel_presentation R M)
    A B D (@freyd_raw_chain_pair_generic R A B D e d chain);

// Fixed-forward equivalence of these same inputs; no object cast is introduced.
symbol freyd_homology_model_native_input_equiv [R : τ CommRing]
  (M : τ (FreydHomologyModel R)) [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@OmegaEquivAlong (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@freyd_homology_model_input R M A B D e d chain)
      (@freyd_raw_chain_native_cone R A B D e d chain)
      (@freyd_homology_model_native_input_map R M A B D e d chain))
≔ @chain_pair_retained_native_equiv (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
    (@freyd_homology_model_kernels R M) (@freyd_homology_model_kernel_presentation R M)
    A B D (@freyd_raw_chain_pair_generic R A B D e d chain);

// Whole H acts on that same map while retaining its original source and target objects.
symbol freyd_homology_model_native_homology_map [R : τ CommRing]
  (M : τ (FreydHomologyModel R)) [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@CommRingFreydHomSet R (@freyd_homology_model_object R M A B D e d chain)
      (@fapp0 _ _ (@freyd_homology_model_func R M) (@freyd_raw_chain_native_cone R A B D e d chain)))
≔ @fapp1_fapp0 _ _ (@freyd_homology_model_func R M)
    (@freyd_homology_model_input R M A B D e d chain)
    (@freyd_raw_chain_native_cone R A B D e d chain)
    (@freyd_homology_model_native_input_map R M A B D e d chain);

// The existing functor action transports the original fixed comparison and inverse laws.
symbol freyd_homology_model_native_homology_equiv [R : τ CommRing]
  (M : τ (FreydHomologyModel R)) [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R)
      (@freyd_homology_model_object R M A B D e d chain)
      (@fapp0 _ _ (@freyd_homology_model_func R M) (@freyd_raw_chain_native_cone R A B D e d chain))
      (@freyd_homology_model_native_homology_map R M A B D e d chain))
≔ @omega_equiv_along_fapp1_fapp0
    (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
    (@CommRingFreydPresentation_cat R) (@freyd_homology_model_func R M)
    (@freyd_homology_model_input R M A B D e d chain)
    (@freyd_raw_chain_native_cone R A B D e d chain)
    (@freyd_homology_model_native_input_map R M A B D e d chain)
    (@freyd_homology_model_native_input_equiv R M A B D e d chain);
