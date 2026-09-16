/* Both column observations retain the original whole input, H objects and selected inverses. */
require open emdash.emdash3_2_commutative_algebra_freyd_column_homology_projection_paths;
symbol K : Cat;
symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
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
symbol E0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0);
symbol E2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2);
symbol x : τ (Obj K);
symbol right_chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1);
symbol left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1);
symbol right_input ≔ (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0
  c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0);
symbol right_comparison ≔ (@freyd_raw_native_right_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1
  i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain);
symbol right_equiv ≔ (@freyd_raw_native_right_column_input_equiv K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain);
symbol right_Hmap ≔ (@freyd_raw_native_right_column_homology_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain);
symbol right_Hequiv ≔ (@freyd_raw_native_right_column_homology_equiv K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1
  p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain);
assert ⊢ right_input : τ (@Transf K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@comp_cat_fapp0 K (@CommRingFreydPresentation_cat R) (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt)) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)));
assert ⊢ sigma_Fst right_comparison ≡ @id (@CommRingFreydPresentation_cat R) D0;
assert ⊢ sigma_Fst (sigma_Snd right_comparison) ≡ @id (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat
  R)) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x);
assert ⊢ right_equiv : τ (@OmegaEquivAlong (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@zero_arrow_family_point_input K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) walking_arrow_tgt)
  (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0
  i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0) x) (@freyd_raw_chain_native_cone R D0 D1 D2 d0 d1
  right_chain) right_comparison);
assert ⊢ right_Hmap : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
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
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R D0 D1 D2
  d0 d1 right_chain)));
assert ⊢ right_Hequiv : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E0)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R D0 D1 D2
  d0 d1 right_chain)) right_Hmap);
assert ⊢ omega_equiv_along_left_inv right_Hequiv ≡ comp_fapp0 (omega_equiv_along_left_inv
  (@homology_family_global_point_equiv K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0) walking_arrow_tgt) (@zero_cone_right_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_right_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E0) x)) (fapp1_fapp0 (@freyd_adjunction_model_func R M) (omega_equiv_along_left_inv
  right_equiv));
symbol left_input ≔ (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0
  c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2);
symbol left_comparison ≔ (@freyd_raw_native_left_column_input_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1
  i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain);
symbol left_equiv ≔ (@freyd_raw_native_left_column_input_equiv K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain);
symbol left_Hmap ≔ (@freyd_raw_native_left_column_homology_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2
  p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain);
symbol left_Hequiv ≔ (@freyd_raw_native_left_column_homology_equiv K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1
  i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain);
assert ⊢ left_input : τ (@Transf K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
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
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)));
assert ⊢ sigma_Fst left_comparison ≡ @id (@CommRingFreydPresentation_cat R) A0;
assert ⊢ sigma_Fst (sigma_Snd left_comparison) ≡ @id (Functor_cat WalkingArrow_cat
  (@CommRingFreydPresentation_cat R)) (@fapp0 K (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat
  R)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) x);
assert ⊢ left_equiv : τ (@OmegaEquivAlong (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@zero_arrow_family_point_input K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0))
  (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A1 B1 D1 i1
  p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2
  i1 p1 i2 p2 a1 b1 d1 c1 c2 f1)) (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1
  p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2) x) (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1
  left_chain) left_comparison);
assert ⊢ left_Hmap : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
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
  c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R A0 A1 A2
  a0 a1 left_chain)));
assert ⊢ left_Hequiv : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K
  (@CommRingFreydPresentation_cat R) (@homology_adjunction_family_func K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E2)) x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R A0 A1 A2
  a0 a1 left_chain)) left_Hmap);
assert ⊢ omega_equiv_along_left_inv left_Hequiv ≡ comp_fapp0 (omega_equiv_along_left_inv
  (@homology_family_global_point_equiv K (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M)
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R A0 B0 D0 i0
  p0 c0)) (@zero_cone_left_column_outgoing_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1) (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 f1))
  (@freyd_raw_native_left_column_input K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1
  b1 d1 f0 f1 middle E2) x)) (fapp1_fapp0 (@freyd_adjunction_model_func R M) (omega_equiv_along_left_inv
  left_equiv));

// Consume the quotient equation at the original row data and actual raw column target.
symbol right_quotient_reconstruction ≔ @freyd_raw_native_right_column_quotient_path K R M
 A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E0 x right_chain;

// Consume the quotient equation at the original row data and actual raw column target.
symbol left_quotient_reconstruction ≔ @freyd_raw_native_left_column_quotient_path K R M
 A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E2 x left_chain;
