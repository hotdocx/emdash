/* Retain the older model's exact H objects by composing its existing input equivalence. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_column_homology_comparisons;
require open emdash.emdash3_2_commutative_algebra_freyd_native_input_comparisons;

// The same native column H maps to the original retained H object.
symbol freyd_retained_right_column_homology_map [K : Cat] [R : τ CommRing] (L : τ (FreydHomologyModel R))
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
  (E : τ (@FreydRawNativeRowShortExact K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 i0 p0 c0))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
  : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
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
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x)
  (@freyd_homology_model_object R L D0 D1 D2 d0 d1 chain))
≔ comp_fapp0 (omega_equiv_along_left_inv (@freyd_homology_model_native_homology_equiv R L D0 D1 D2 d0 d1 chain))
  (@freyd_raw_native_right_column_homology_map K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1 A2
  B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain);

// Reverse the existing selected comparison, then compose existing equivalences.
symbol freyd_retained_right_column_homology_equiv [K : Cat] [R : τ CommRing] (L : τ (FreydHomologyModel R))
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
  (E : τ (@FreydRawNativeRowShortExact K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 i0 p0 c0))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R D0 D1 D2 d0 d1))
  : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
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
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x)
  (@freyd_homology_model_object R L D0 D1 D2 d0 d1 chain) (@freyd_retained_right_column_homology_map K R L A0 B0
  D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain))
≔ omega_equiv_along_comp (@freyd_raw_native_right_column_homology_map K R (@freyd_homology_model_adjunctions R
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain)
  (omega_equiv_along_left_inv (@freyd_homology_model_native_homology_equiv R L D0 D1 D2 d0 d1 chain))
  (@freyd_raw_native_right_column_homology_equiv K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1
  A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain) (iso_evidence_omega_along
  (iso_evidence_sym (omega_equiv_along_iso_evidence (@freyd_homology_model_native_homology_map R L D0 D1 D2 d0
  d1 chain) (@freyd_homology_model_native_homology_equiv R L D0 D1 D2 d0 d1 chain))));

// The same native column H maps to the original retained H object.
symbol freyd_retained_left_column_homology_map [K : Cat] [R : τ CommRing] (L : τ (FreydHomologyModel R))
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
  (E : τ (@FreydRawNativeRowShortExact K R (@freyd_homology_model_adjunctions R L) A2 B2 D2 i2 p2 c2))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
  : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
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
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x)
  (@freyd_homology_model_object R L A0 A1 A2 a0 a1 chain))
≔ comp_fapp0 (omega_equiv_along_left_inv (@freyd_homology_model_native_homology_equiv R L A0 A1 A2 a0 a1 chain))
  (@freyd_raw_native_left_column_homology_map K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1 A2
  B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain);

// Reverse the existing selected comparison, then compose existing equivalences.
symbol freyd_retained_left_column_homology_equiv [K : Cat] [R : τ CommRing] (L : τ (FreydHomologyModel R))
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
  (E : τ (@FreydRawNativeRowShortExact K R (@freyd_homology_model_adjunctions R L) A2 B2 D2 i2 p2 c2))
  (x : τ (Obj K))
  (chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
  : τ (@OmegaEquivAlong (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R)
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
  L) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E)) x)
  (@freyd_homology_model_object R L A0 A1 A2 a0 a1 chain) (@freyd_retained_left_column_homology_map K R L A0 B0
  D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain))
≔ omega_equiv_along_comp (@freyd_raw_native_left_column_homology_map K R (@freyd_homology_model_adjunctions R L)
  A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain)
  (omega_equiv_along_left_inv (@freyd_homology_model_native_homology_equiv R L A0 A1 A2 a0 a1 chain))
  (@freyd_raw_native_left_column_homology_equiv K R (@freyd_homology_model_adjunctions R L) A0 B0 D0 A1 B1 D1 A2
  B2 D2 i0 p0 i1 p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 f0 f1 middle E x chain) (iso_evidence_omega_along
  (iso_evidence_sym (omega_equiv_along_iso_evidence (@freyd_homology_model_native_homology_map R L A0 A1 A2 a0
  a1 chain) (@freyd_homology_model_native_homology_equiv R L A0 A1 A2 a0 a1 chain))));
