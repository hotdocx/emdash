/* Whole normality enhancement of the original native model. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_models;
require open emdash.emdash3_2_commutative_algebra_freyd_additive;
require open emdash.emdash3_2_one_cat_adjunction_normality;

// Existing fixed-forward whole normality. Retain the literal additive
// projections used by the generic δ/exactness owners; reducing their spelling
// here makes later comparison of the dependent normality type expensive.
symbol FreydAdjunctionModelNormality [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) : Grpd
≔ @OneCatAdjunctionNormality (@CommRingFreydPresentation_cat R)
        (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
        (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
    (@freyd_adjunction_model_initial R M)
    (@freyd_adjunction_model_kernels R M)
    (@freyd_adjunction_model_cokernels R M);
