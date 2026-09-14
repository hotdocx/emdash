/* Original raw rows supply the existing whole column inputs and incoming observations. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_short_exact;
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_zeros;
require open emdash.emdash3_2_one_cat_zero_cone_column_inputs;
require open emdash.emdash3_2_one_cat_kernel_family_point_paths;

// Whole right input from the same three rows and their derived zero.
symbol freyd_raw_native_right_column_input [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@Transf K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 K
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
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)))
≔ @one_cat_zero_cone_right_column_input K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E;

// Point recovery is an observation of the existing whole source law.
symbol freyd_raw_native_right_column_incoming_path [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@= (Hom (@CommRingFreydPresentation_cat R) D0 D1) (@terminal_arrow_test_incoming
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@fapp0 K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt) x)
  (@fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
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
  i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E))) (@comm_ring_freyd_hom_class R D0 D1 d0))
≔ @one_cat_kernel_family_point_incoming_path K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0) walking_arrow_tgt)
  (@one_cat_zero_cone_right_column_zero_path K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E) x;

// Whole left input from the same three rows and their derived zero.
symbol freyd_raw_native_left_column_input [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@Transf K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@comp_cat_fapp0 K
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
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)))
≔ @one_cat_zero_cone_left_column_input K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E;

// Point recovery is an observation of the existing whole source law.
symbol freyd_raw_native_left_column_incoming_path [K : Cat] [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@= (Hom (@CommRingFreydPresentation_cat R) A0 A1) (@terminal_arrow_test_incoming
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@fapp0 K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_source_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0)) x) (@fapp0 K (Functor_cat
  WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@zero_cone_left_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2
  p2 a1 b1 d1 c1 c2 f1)) x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@comp_cat_fapp0 K (@CommRingFreydPresentation_cat R) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0))) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E))) (@comm_ring_freyd_hom_class R A0 A1 a0))
≔ @one_cat_kernel_family_point_incoming_path K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0))
  (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) (@zero_cone_row_family_source_map K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0))
  (@one_cat_zero_cone_left_column_zero_path K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K
  R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2
  B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 f0)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2 f0 f1 middle) E) x;
