/* Model-specialized exactness of the three original native-window comparisons.
   These transparent partial applications retain the original dependent
   telescope, fixed comparison, and selected inverse evidence. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_connecting;
require open emdash.emdash3_2_one_cat_native_middle_homology_exactness;
require open emdash.emdash3_2_one_cat_connecting_source_exactness;
require open emdash.emdash3_2_one_cat_connecting_target_exactness;

// Exactness at the middle position, with the actual fixed comparison.
symbol freyd_adjunction_model_middle_exact_omega [B : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
≔ @one_cat_native_window_middle_exact_omega B (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N;

// Exactness at the source position, with the actual fixed comparison.
symbol freyd_adjunction_model_source_exact_omega [B : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
≔ @one_cat_native_window_source_exact_omega B (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N;

// Exactness at the target position, with the actual fixed comparison.
symbol freyd_adjunction_model_target_exact_omega [B : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
≔ @one_cat_native_window_target_exact_omega B (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N;
