/* Categorical input comparisons retain each original raw column chain witness. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_column_inputs;
require open emdash.emdash3_2_one_cat_introduced_terminal_input_comparisons;
require open emdash.emdash3_2_zero_arrow_family_point_inputs;

// Preserve both actual input objects and the original raw chain witness.
symbol freyd_raw_native_right_column_input_map [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (Hom (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
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
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1 chain))
≔ @one_cat_introduced_terminal_input_comparison_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) walking_arrow_tgt)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2 B2 D2 i2
  p2 c2) walking_arrow_tgt) (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1) walking_arrow_tgt) x (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) x) (@comm_ring_freyd_hom_class R D0 D1
  d0) (@freyd_raw_chain_zero_path R D0 D1 D2 d0 d1 chain) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 K (@CommRingFreydPresentation_cat R) (Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@terminal_arrow_diagram_func
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R))) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt))
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) (@freyd_raw_native_right_column_incoming_path K R M A0
  B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x);

// Existing fixed-map equivalence, with the same selected inverse.
symbol freyd_raw_native_right_column_input_equiv [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@OmegaEquivAlong (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
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
  a1 b1 d1 f0 f1 middle E x chain))
≔ @one_cat_introduced_terminal_input_comparison_equiv K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) walking_arrow_tgt) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) walking_arrow_tgt) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1) walking_arrow_tgt) x (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) x) (@comm_ring_freyd_hom_class R D0 D1 d0) (@freyd_raw_chain_zero_path R D0 D1 D2 d0
  d1 chain) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 K
  (@CommRingFreydPresentation_cat R) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt))
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) (@freyd_raw_native_right_column_incoming_path K R M A0
  B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x);

// Preserve both actual input objects and the original raw chain witness.
symbol freyd_raw_native_left_column_input_map [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (Hom (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
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
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E) x) (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1 chain))
≔ @one_cat_introduced_terminal_input_comparison_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1))
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2 B2 D2 i2
  p2 c2)) (@zero_cone_row_family_source_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) x) (@comm_ring_freyd_hom_class R A0 A1 a0) (@freyd_raw_chain_zero_path R A0 A1 A2 a0 a1 chain)
  (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 K
  (@CommRingFreydPresentation_cat R) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)))
  (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) (@freyd_raw_native_left_column_incoming_path K R M A0
  B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x);

// Existing fixed-map equivalence, with the same selected inverse.
symbol freyd_raw_native_left_column_input_equiv [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@OmegaEquivAlong (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_arrow_family_point_input K
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
  a1 b1 d1 f0 f1 middle E x chain))
≔ @one_cat_introduced_terminal_input_comparison_equiv K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1)) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A2 B2 D2 i2
  p2 c2)) (@zero_cone_row_family_source_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) x) (@comm_ring_freyd_hom_class R A0 A1 a0) (@freyd_raw_chain_zero_path R A0 A1 A2 a0 a1 chain)
  (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 K
  (@CommRingFreydPresentation_cat R) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)))
  (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) (@freyd_raw_native_left_column_incoming_path K R M A0
  B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x);
