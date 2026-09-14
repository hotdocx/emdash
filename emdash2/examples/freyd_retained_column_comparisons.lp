/* The original retained-model H objects are the literal comparison targets. */
require open emdash.emdash3_2_commutative_algebra_freyd_retained_column_homology_comparisons;
symbol K : Cat;
symbol R : τ CommRing;
symbol L : τ (FreydHomologyModel R);
symbol A0 : τ (@CommRingPresentation R);
symbol B0 : τ (@CommRingPresentation R);
symbol D0 : τ (@CommRingPresentation R);
symbol A1 : τ (@CommRingPresentation R);
symbol B1 : τ (@CommRingPresentation R);
symbol D1 : τ (@CommRingPresentation R);
symbol A2 : τ (@CommRingPresentation R);
symbol B2 : τ (@CommRingPresentation R);
symbol D2 : τ (@CommRingPresentation R);
symbol i0 : τ (@CommRingPresentationMorphism R A0 B0);
symbol p0 : τ (@CommRingPresentationMorphism R B0 D0);
symbol i1 : τ (@CommRingPresentationMorphism R A1 B1);
symbol p1 : τ (@CommRingPresentationMorphism R B1 D1);
symbol i2 : τ (@CommRingPresentationMorphism R A2 B2);
symbol p2 : τ (@CommRingPresentationMorphism R B2 D2);
symbol c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0);
symbol c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1);
symbol c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2);
symbol a0 : τ (@CommRingPresentationMorphism R A0 A1);
symbol b0 : τ (@CommRingPresentationMorphism R B0 B1);
symbol d0 : τ (@CommRingPresentationMorphism R D0 D1);
symbol a1 : τ (@CommRingPresentationMorphism R A1 A2);
symbol b1 : τ (@CommRingPresentationMorphism R B1 B2);
symbol d1 : τ (@CommRingPresentationMorphism R D1 D2);
symbol f0 : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0);
symbol f1 : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1);
symbol middle : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1);
symbol E0 : τ (@FreydRawNativeRowShortExact K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 i0 p0 c0);
symbol E2 : τ (@FreydRawNativeRowShortExact K R (@freyd_homology_model_adjunctions R L) A2 B2 D2 i2 p2 c2);
symbol x : τ (Obj K);
symbol right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1);
symbol left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1);
symbol right_map ≔ @freyd_retained_right_column_homology_map K R L A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain;
symbol right_equiv ≔ @freyd_retained_right_column_homology_equiv K R L A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain;
assert ⊢ right_map : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R (@freyd_homology_model_adjunctions R L))
  (@freyd_adjunction_model_kernels R (@freyd_homology_model_adjunctions R L)) (@freyd_adjunction_model_cokernels
  R (@freyd_homology_model_adjunctions R L)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R (@freyd_homology_model_adjunctions R
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0)) x)
  (@freyd_homology_model_object R L D0 D1 D2 d0 d1 right_chain));
assert ⊢ right_equiv : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R
  (@freyd_homology_model_adjunctions R L)) (@freyd_adjunction_model_kernels R (@freyd_homology_model_adjunctions
  R L)) (@freyd_adjunction_model_cokernels R (@freyd_homology_model_adjunctions R L))
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1 A2 B2 D2
  i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0)) x) (@freyd_homology_model_object R L D0 D1 D2
  d0 d1 right_chain) right_map);
assert ⊢ omega_equiv_along_left_inv right_equiv ≡ comp_fapp0 (omega_equiv_along_left_inv
  (@freyd_raw_native_right_column_homology_equiv K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1
  A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain))
  (@freyd_homology_model_native_homology_map R L D0 D1 D2 d0 d1 right_chain);
symbol left_map ≔ @freyd_retained_left_column_homology_map K R L A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0
  c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain;
symbol left_equiv ≔ @freyd_retained_left_column_homology_equiv K R L A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain;
assert ⊢ left_map : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
  (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R (@freyd_homology_model_adjunctions R L))
  (@freyd_adjunction_model_kernels R (@freyd_homology_model_adjunctions R L)) (@freyd_adjunction_model_cokernels
  R (@freyd_homology_model_adjunctions R L)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0))
  (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R (@freyd_homology_model_adjunctions R
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2)) x)
  (@freyd_homology_model_object R L A0 A1 A2 a0 a1 left_chain));
assert ⊢ left_equiv : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R
  (@freyd_homology_model_adjunctions R L)) (@freyd_adjunction_model_kernels R (@freyd_homology_model_adjunctions
  R L)) (@freyd_adjunction_model_cokernels R (@freyd_homology_model_adjunctions R L))
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0
  p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2)) x) (@freyd_homology_model_object R L A0 A1 A2 a0
  a1 left_chain) left_map);
assert ⊢ omega_equiv_along_left_inv left_equiv ≡ comp_fapp0 (omega_equiv_along_left_inv
  (@freyd_raw_native_left_column_homology_equiv K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1 A2
  B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain))
  (@freyd_homology_model_native_homology_map R L A0 A1 A2 a0 a1 left_chain);
