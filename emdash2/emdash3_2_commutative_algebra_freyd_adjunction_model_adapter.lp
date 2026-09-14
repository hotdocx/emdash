/* One-way interpretation adapter. Whole P/Q and H retain their original
   values; the old pointwise normality is not promoted to whole normality. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_models;
require open emdash.emdash3_2_commutative_algebra_freyd_homology_models;

symbol freyd_homology_model_adjunctions [R : τ CommRing]
  (M : τ (FreydHomologyModel R)) : τ (FreydAdjunctionModel R)
≔ @freyd_adjunction_model_intro R (@freyd_homology_model_initial R M)
    (@kernel_presentation_structure (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
      (@comm_ring_freyd_terminal_zero R) (@freyd_homology_model_kernels R M)
      (@freyd_homology_model_kernel_presentation R M))
    (@cokernel_presentation_structure (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
      (@freyd_homology_model_initial R M) (@freyd_homology_model_cokernels R M)
      (@freyd_homology_model_cokernel_presentation R M));
