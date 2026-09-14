/* Reviewer hypotheses are one supplied native model and its original whole window. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_exactness;

symbol B : Cat;
symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
symbol N : τ (@FreydAdjunctionModelNormality R M);
symbol Rm : τ (Functor B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))));
symbol R0 : τ (Functor B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))));
symbol R1 : τ (Functor B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))));
symbol R2 : τ (Functor B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))));
symbol mm : τ (@Transf B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) Rm R0);
symbol m0 : τ (@Transf B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) R0 R1);
symbol m1 : τ (@Transf B (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) R1 R2);
symbol upper_zero : τ (@= (@Transf B (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat B
  (@CommRingFreydPresentation_cat R)) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_map B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0 walking_arrow_src) (@zero_cone_row_family_vertex_map B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm R0
  mm walking_arrow_src)) (@zero_arrow_family_zero_transf B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R1
  walking_arrow_src)));
symbol lower_zero : τ (@= (@Transf B (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat B
  (@CommRingFreydPresentation_cat R)) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_map B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R1 R2
  m1 walking_arrow_src) (@zero_cone_row_family_vertex_map B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0 walking_arrow_src)) (@zero_arrow_family_zero_transf B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R2
  walking_arrow_src)));
symbol Em : τ (@OneCatZeroConeShortExactFamily B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm);
symbol E0 : τ (@OneCatZeroConeShortExactFamily B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) R0);
symbol E1 : τ (@OneCatZeroConeShortExactFamily B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) R1);
symbol E2 : τ (@OneCatZeroConeShortExactFamily B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) R2);
symbol x : τ (Obj B);
symbol y : τ (Obj B);

// Whole δ at the original H source and target.
assert ⊢ (@freyd_adjunction_model_connecting_transf B R M N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1
  E2) : τ (@Transf B (@CommRingFreydPresentation_cat R) (@one_cat_native_window_source_homology_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2));

// Whole off-diagonal Hom action remains available.
assert ⊢ @one_cat_native_window_connecting_reconstruction B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2 : τ (@=
  (@Transf B (@CommRingFreydPresentation_cat R) (@kernel_precomposition_family_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_kernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0
  walking_arrow_src) (@zero_cone_right_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@zero_cone_row_family_outgoing B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0))
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@comp_fapp0 (Functor_cat B (@CommRingFreydPresentation_cat R))
  (@kernel_precomposition_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@zero_cone_row_family_vertex_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) R0 walking_arrow_src) (@zero_cone_right_column_outgoing_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) R0 R1 m0) (@zero_cone_row_family_outgoing B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0))
  (@one_cat_native_window_source_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@freyd_adjunction_model_connecting_transf B R M N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_cover_transf B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_covered_transf B (@CommRingFreydPresentation_cat
  R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2));

// Source exactness retains the actual comparison.
assert ⊢ @iso_evidence_to (Functor_cat B (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@CommRingFreydPresentation_cat R)
  (@adjunction_image_func (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M)) (@zero_arrow_family_incoming_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@one_cat_native_window_middle_source_homology_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_source_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@freyd_adjunction_model_connecting_transf B R M N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_native_window_source_exact_input B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@kernel_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func B
  (@CommRingFreydPresentation_cat R) (@one_cat_native_window_source_homology_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@freyd_adjunction_model_connecting_transf B R M N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@omega_equiv_along_iso_evidence (Functor_cat B
  (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@CommRingFreydPresentation_cat R) (@adjunction_image_func
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M)) (@zero_arrow_family_incoming_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@one_cat_native_window_middle_source_homology_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_source_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@freyd_adjunction_model_connecting_transf B R M N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  (@one_cat_native_window_source_exact_input B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)))
  (@kernel_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func B
  (@CommRingFreydPresentation_cat R) (@one_cat_native_window_source_homology_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@freyd_adjunction_model_connecting_transf B R M N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_source_exact_comparison B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@freyd_adjunction_model_source_exact_omega B R M N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) ≡ (@one_cat_native_window_source_exact_comparison B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2);

// Middle exactness retains the actual comparison.
assert ⊢ @iso_evidence_to (Functor_cat B (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@CommRingFreydPresentation_cat R)
  (@adjunction_image_func (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M)) (@zero_arrow_family_incoming_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_source_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm)
  (@zero_cone_left_column_outgoing_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1 m0)
  (@one_cat_zero_cone_left_column_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero E1))
  (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@one_cat_zero_cone_middle_column_input B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) Rm R0 R1 mm m0 upper_zero))
  (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@one_cat_zero_cone_right_column_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em))
  (@one_cat_row_triple_outgoing_homology_map B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em
  E0 E1)) (@one_cat_row_triple_homology_zero_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em
  E0 E1))) (@kernel_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func B
  (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) Rm R0 R1 mm m0 upper_zero))
  (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@one_cat_zero_cone_right_column_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em))
  (@one_cat_row_triple_outgoing_homology_map B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em
  E0 E1))) (@omega_equiv_along_iso_evidence (Functor_cat B (@CommRingFreydPresentation_cat R))
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@CommRingFreydPresentation_cat R) (@adjunction_image_func (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M))
  (@zero_arrow_family_incoming_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@homology_adjunction_family_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_source_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm)
  (@zero_cone_left_column_outgoing_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1 m0)
  (@one_cat_zero_cone_left_column_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero E1))
  (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func B
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_src) (@zero_cone_middle_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@one_cat_zero_cone_middle_column_input B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) Rm R0 R1 mm m0 upper_zero))
  (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@one_cat_zero_cone_right_column_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em))
  (@one_cat_row_triple_outgoing_homology_map B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em
  E0 E1)) (@one_cat_row_triple_homology_zero_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em
  E0 E1))) (@kernel_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M) (@transf_arrow_diagram_func B
  (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm walking_arrow_src)
  (@zero_cone_middle_column_outgoing_func B (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1 m0)
  (@one_cat_zero_cone_middle_column_input B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) Rm R0 R1 mm m0 upper_zero))
  (@homology_adjunction_family_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Rm
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func B (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) R0 R1
  m0) (@one_cat_zero_cone_right_column_input B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em))
  (@one_cat_row_triple_outgoing_homology_map B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 mm m0 upper_zero Em
  E0 E1))) (@one_cat_native_window_middle_exact_comparison B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2)
  (@freyd_adjunction_model_middle_exact_omega B R M N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2))
  ≡ (@one_cat_native_window_middle_exact_comparison B (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero Em E0 E1 E2);

// Target exactness retains the actual comparison.
assert ⊢ @iso_evidence_to (Functor_cat B (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@CommRingFreydPresentation_cat R)
  (@adjunction_image_func (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M)) (@zero_arrow_family_incoming_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@one_cat_native_window_source_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_func B (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@omega_equiv_along_iso_evidence (Functor_cat B
  (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@CommRingFreydPresentation_cat R) (@adjunction_image_func
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M)) (@zero_arrow_family_incoming_func B (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@one_cat_native_window_source_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) (@one_cat_native_window_target_exact_input B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@kernel_adjunction_family_func B (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_kernels R M)
  (@transf_arrow_diagram_func B (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_target_homology_func B (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_middle_target_homology_func B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@one_cat_native_window_homology_inclusion B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2))) (@one_cat_native_window_target_exact_comparison B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2) (@freyd_adjunction_model_target_exact_omega B R M N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2)) ≡ (@one_cat_native_window_target_exact_comparison B
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N Rm R0 R1 R2 mm m0 m1
  upper_zero lower_zero Em E0 E1 E2);
