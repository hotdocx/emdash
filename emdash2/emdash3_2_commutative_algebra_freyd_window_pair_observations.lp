/* Observe the original zero-pair inputs of native window exactness.
   Whole canonical Im→Ker and its proof remain owned by the existing window
   theorems. These definitions expose their input arrows, not output exactness. */
require open emdash.emdash3_2_zero_arrow_pair_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_raw_window_connecting;
require open emdash.emdash3_2_one_cat_native_homology_window_exact_inputs;

// Original middle exactness input, observed at x.
symbol freyd_raw_native_window_middle_pair_at [K : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydRawNativeRowShortExact K R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))

  (x : τ (Obj K))
  : τ (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ @zero_arrow_family_pair_at K
  (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation
    R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R))
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm))
  (@one_cat_zero_cone_left_column_input K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) x1))
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) walking_arrow_src) (@zero_cone_middle_column_outgoing_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm)) (@one_cat_zero_cone_middle_column_input K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper)))
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm)
  walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm))
  (@one_cat_zero_cone_right_column_input K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) xm))
  (@one_cat_row_triple_outgoing_homology_map K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) xm x0 x1))
  (@one_cat_row_triple_homology_zero_input K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) xm x0 x1)
  x;

// Original source exactness input, observed at x.
symbol freyd_raw_native_window_source_pair_at [K : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydRawNativeRowShortExact K R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))

  (x : τ (Obj K))
  : τ (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ @zero_arrow_family_pair_at K
  (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation
    R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R)
  (@comm_ring_freyd_additive R))
  (@one_cat_native_window_middle_source_homology_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R)
  (@one_cat_native_window_source_homology_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  (@one_cat_native_window_target_homology_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  (@one_cat_native_window_connecting_transf K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm
  x0 x1 x2))
  (@one_cat_native_window_source_exact_input K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  x;

// Original target exactness input, observed at x.
symbol freyd_raw_native_window_target_pair_at [K : Cat] [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  (N : τ (@FreydAdjunctionModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydRawNativeRowShortExact K R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))

  (x : τ (Obj K))
  : τ (ArrowPairObservation (@CommRingFreydPresentation_cat R))
≔ @zero_arrow_family_pair_at K
  (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation
    R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R)
  (@comm_ring_freyd_additive R))
  (@one_cat_native_window_source_homology_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  (@transf_arrow_diagram_func K (@CommRingFreydPresentation_cat R) (@one_cat_native_window_target_homology_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation
    R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  (@one_cat_native_window_middle_target_homology_func K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2) (@one_cat_native_window_homology_inclusion K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N (@freyd_raw_native_row_family K R Am Bm Dm im pm cm)
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2))
  (@one_cat_native_window_target_exact_input K (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation
    R) (@comm_ring_freyd_additive R) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels
    R M) (@freyd_adjunction_model_cokernels R M) N (@freyd_raw_native_row_family K R Am Bm Dm im pm cm) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2)
  x;
