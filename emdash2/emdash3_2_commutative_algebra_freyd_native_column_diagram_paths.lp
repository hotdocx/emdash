/* Compare actual native diagram actions at the three retained columns. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_middle_column_comparisons;
require open emdash.emdash3_2_commutative_algebra_freyd_native_column_input_comparisons;
require open emdash.emdash3_2_one_cat_row_homology_maps;
require open emdash.emdash3_2_one_cat_diagram_map_paths;
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_point_paths;

// Ordinary diagram faithfulness retains both actual diagram endpoints.
symbol freyd_native_column_incoming_diagram_path [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel
  R))
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

 (E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2)) (x : τ (Obj K))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (column_map : τ (@CommRingFreydHomologyChainMap R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2))
 : τ (@= (@Transf WalkingArrow_cat (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle))) (@comp_fapp0 (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R A0 A1
  A2 a0 a1 left_chain)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R A0 A1
  A2 a0 a1 left_chain) (@freyd_raw_chain_native_cone R B0 B1 B2 b0 b1 middle) (@freyd_raw_chain_native_map
  R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2 left_chain middle column_map)) (@fapp1_fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x) (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1 left_chain)
  (@freyd_raw_native_left_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0
  b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain))) (@comp_fapp0 (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x) (@freyd_raw_chain_native_cone R B0 B1 B2 b0 b1 middle)
  (@freyd_raw_native_middle_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2
  a0 b0 d0 a1 b1 d1 f0 f1 middle x)) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@zero_cone_middle_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x
  (@one_cat_row_triple_incoming_diagram_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family
  K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2
  i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E0 E1 E2))))
≔ @one_cat_diagram_map_path (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@comp_fapp0 (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R A0 A1
  A2 a0 a1 left_chain)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R A0 A1
  A2 a0 a1 left_chain) (@freyd_raw_chain_native_cone R B0 B1 B2 b0 b1 middle) (@freyd_raw_chain_native_map
  R A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 i0 i1 i2 left_chain middle column_map)) (@fapp1_fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x) (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1 left_chain)
  (@freyd_raw_native_left_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0
  b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain))) (@comp_fapp0 (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E2) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x) (@freyd_raw_chain_native_cone R B0 B1 B2 b0 b1 middle)
  (@freyd_raw_native_middle_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2
  a0 b0 d0 a1 b1 d1 f0 f1 middle x)) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@zero_cone_middle_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x
  (@one_cat_row_triple_incoming_diagram_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family
  K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2
  i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E0 E1 E2)))
 (@eq_trans _ _ _ _ (@eq_refl (Hom (@CommRingFreydPresentation_cat R) A1 B1) (@comm_ring_freyd_hom_class R
  A1 B1 i1)) (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_refl (Hom (@CommRingFreydPresentation_cat R) A1 B1)
  (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1)) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) walking_arrow_src) x (@one_cat_zero_cone_row_family_incoming K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1)))) (@freyd_native_row_incoming_at_path K R A1 B1 D1 i1 p1 c1 x)))) (@eq_trans _ _ _ _
  (@eq_refl (Hom (@CommRingFreydPresentation_cat R) A2 B2) (@comm_ring_freyd_hom_class R A2 B2 i2))
  (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_refl (Hom (@CommRingFreydPresentation_cat R) A2 B2) (@tapp0_fapp0
  K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2)) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) walking_arrow_src) x (@one_cat_zero_cone_row_family_incoming K
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2)))) (@freyd_native_row_incoming_at_path K R A2 B2 D2 i2 p2 c2 x))));

// Ordinary diagram faithfulness retains both actual diagram endpoints.
symbol freyd_native_column_outgoing_diagram_path [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel
  R))
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

 (E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
 (E1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
 (E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2)) (x : τ (Obj K))
 (left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
 (right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
 (column_map : τ (@CommRingFreydHomologyChainMap R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2))
 : τ (@= (@Transf WalkingArrow_cat (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R D0 D1
  D2 d0 d1 right_chain))) (@comp_fapp0 (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R D0 D1
  D2 d0 d1 right_chain)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 right_chain)
  (@freyd_raw_chain_native_map R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2 middle right_chain column_map))
  (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x) (@freyd_raw_chain_native_cone R B0 B1 B2 b0 b1 middle)
  (@freyd_raw_native_middle_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2
  a0 b0 d0 a1 b1 d1 f0 f1 middle x))) (@comp_fapp0 (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E0) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R D0 D1
  D2 d0 d1 right_chain)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E0) x) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 right_chain)
  (@freyd_raw_native_right_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0
  b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain)) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x
  (@one_cat_row_triple_outgoing_diagram_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family
  K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2
  i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E0 E1 E2))))
≔ @one_cat_diagram_map_path (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R D0 D1
  D2 d0 d1 right_chain)) (@comp_fapp0 (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R D0 D1
  D2 d0 d1 right_chain)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R B0 B1
  B2 b0 b1 middle) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 right_chain)
  (@freyd_raw_chain_native_map R B0 B1 B2 D0 D1 D2 b0 b1 d0 d1 p0 p1 p2 middle right_chain column_map))
  (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x) (@freyd_raw_chain_native_cone R B0 B1 B2 b0 b1 middle)
  (@freyd_raw_native_middle_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2
  a0 b0 d0 a1 b1 d1 f0 f1 middle x))) (@comp_fapp0 (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_middle_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E0) x)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@freyd_raw_chain_native_cone R D0 D1
  D2 d0 d1 right_chain)) (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0
  d0 a1 b1 d1 f0 f1 middle E0) x) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 right_chain)
  (@freyd_raw_native_right_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0
  b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain)) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x
  (@one_cat_row_triple_outgoing_diagram_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family
  K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2
  i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E0 E1 E2)))
 (@eq_trans _ _ _ _ (@eq_refl (Hom (@CommRingFreydPresentation_cat R) B1 D1) (@comm_ring_freyd_hom_class R
  B1 D1 p1)) (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_refl (Hom (@CommRingFreydPresentation_cat R) B1 D1)
  (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1) walking_arrow_tgt) x (@zero_cone_row_family_outgoing K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1
  D1 i1 p1 c1)))) (@freyd_native_row_outgoing_at_path K R A1 B1 D1 i1 p1 c1 x)))) (@eq_trans _ _ _ _
  (@eq_refl (Hom (@CommRingFreydPresentation_cat R) B2 D2) (@comm_ring_freyd_hom_class R B2 D2 p2))
  (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_refl (Hom (@CommRingFreydPresentation_cat R) B2 D2) (@tapp0_fapp0
  K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) walking_arrow_tgt) x (@zero_cone_row_family_outgoing K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2)))) (@freyd_native_row_outgoing_at_path K R A2 B2 D2 i2 p2 c2 x))));
