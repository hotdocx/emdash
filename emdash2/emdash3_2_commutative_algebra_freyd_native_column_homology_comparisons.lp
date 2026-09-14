/* Whole H acts on the existing column comparisons, with its original selected inverses. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_column_input_comparisons;
require open emdash.emdash3_2_homology_family_point_comparisons;
require open emdash.emdash3_2_omega_equiv_composition;

// Original H-family point → H of the original raw column input.
symbol freyd_raw_native_right_column_homology_map [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
  (E : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
  : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R D0 D1 D2
  d0 d1 chain)))
≔ @comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R D0 D1 D2
  d0 d1 chain)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 chain)
  (@freyd_raw_native_right_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0
  a1 b1 d1 f0 f1 middle E x chain)) (@homology_family_global_point_map K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels
  R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E) x);

// Compose the same two categorical equivalences using existing owners.
symbol freyd_raw_native_right_column_homology_equiv [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
  (E : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
  : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R D0 D1 D2
  d0 d1 chain)) (@freyd_raw_native_right_column_homology_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain))
≔ omega_equiv_along_comp (@homology_family_global_point_map K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels
  R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E) x) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 chain)
  (@freyd_raw_native_right_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0
  a1 b1 d1 f0 f1 middle E x chain)) (@homology_family_global_point_equiv K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels
  R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E) x) (omega_equiv_along_fapp1_fapp0 (@freyd_adjunction_model_func R M)
  (@freyd_raw_native_right_column_input_equiv K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E x chain));

// Original H-family point → H of the original raw column input.
symbol freyd_raw_native_left_column_homology_map [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
  (E : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
  : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R A0 A1 A2
  a0 a1 chain)))
≔ @comp_fapp0 (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R A0 A1 A2
  a0 a1 chain)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x) (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1 chain)
  (@freyd_raw_native_left_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0
  a1 b1 d1 f0 f1 middle E x chain)) (@homology_family_global_point_map K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels
  R M) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E) x);

// Compose the same two categorical equivalences using existing owners.
symbol freyd_raw_native_left_column_homology_equiv [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (@CommRingPresentation R)]
  [i0 : τ (@CommRingPresentationMorphism R A0 B0)]
  [p0 : τ (@CommRingPresentationMorphism R B0 D0)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 D1)]
  [i2 : τ (@CommRingPresentationMorphism R A2 B2)]
  [p2 : τ (@CommRingPresentationMorphism R B2 D2)]
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  [a0 : τ (@CommRingPresentationMorphism R A0 A1)]
  [b0 : τ (@CommRingPresentationMorphism R B0 B1)]
  [d0 : τ (@CommRingPresentationMorphism R D0 D1)]
  [a1 : τ (@CommRingPresentationMorphism R A1 A2)]
  [b1 : τ (@CommRingPresentationMorphism R B1 B2)]
  [d1 : τ (@CommRingPresentationMorphism R D1 D2)]
  (f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
  (E : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
  : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R A0 A1 A2
  a0 a1 chain)) (@freyd_raw_native_left_column_homology_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain))
≔ omega_equiv_along_comp (@homology_family_global_point_map K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels
  R M) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E) x) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x) (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1 chain)
  (@freyd_raw_native_left_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0
  a1 b1 d1 f0 f1 middle E x chain)) (@homology_family_global_point_equiv K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels
  R M) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E) x) (omega_equiv_along_fapp1_fapp0 (@freyd_adjunction_model_func R M)
  (@freyd_raw_native_left_column_input_equiv K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E x chain));
