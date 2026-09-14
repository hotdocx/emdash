/* Specialization of the existing whole owner; every row, map and chosen inverse is retained. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;
require open emdash.emdash3_2_one_cat_native_homology_window_connecting;

// Transparent partial application; the remaining telescope is the original
// whole window interface and the result is its actual H_C⇒H_A transformation.
symbol freyd_adjunction_model_connecting_transf [B : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
≔ @one_cat_native_window_connecting_transf B (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N;
