/* Native row shortness is supplied model structure at the actual whole P/Q. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_models;
require open emdash.emdash3_2_commutative_algebra_freyd_additive;
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_families;
require open emdash.emdash3_2_one_cat_zero_cone_row_families;

symbol FreydRawNativeRowShortExact [K : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) [X Y Z0 : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R X Y))
  (d : τ (@CommRingPresentationMorphism R Y Z0))
  (chain : τ (@CommRingFreydChainPair R X Y Z0 e d)) : Grpd
≔ @OneCatZeroConeShortExactFamily K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K
  R X Y Z0 e d chain);
