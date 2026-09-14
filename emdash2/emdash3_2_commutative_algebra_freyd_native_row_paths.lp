/* Whole original row projections, compared with their literal raw morphisms. */
require open emdash.emdash3_2_one_cat_constant_transformation_views;
require open emdash.emdash3_2_one_cat_zero_cone_row_families;
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_families;

// Retain the original whole first projection and its raw arrow.
symbol freyd_raw_native_row_first_whole_path [K : Cat] [R : τ CommRing]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  (chainS : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd))
  (chainT : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td))
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : τ (@= (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S2)
  (@Const_func K (@CommRingFreydPresentation_cat R) T2)) (@zero_cone_row_family_source_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext
  td chainT) (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m))
  (@Const_transf K (@CommRingFreydPresentation_cat R) S2 T2 (@comm_ring_freyd_hom_class R S2 T2 f2)))
≔ @eq_refl (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S2)
  (@Const_func K (@CommRingFreydPresentation_cat R) T2)) (@zero_cone_row_family_source_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext
  td chainT) (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m));

// Retain the original whole middle projection and its raw arrow.
symbol freyd_raw_native_row_middle_whole_path [K : Cat] [R : τ CommRing]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  (chainS : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd))
  (chainT : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td))
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : τ (@= (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S1)
  (@Const_func K (@CommRingFreydPresentation_cat R) T1)) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext
  td chainT) (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  walking_arrow_src) (@Const_transf K (@CommRingFreydPresentation_cat R) S1 T1 (@comm_ring_freyd_hom_class R S1
  T1 f1)))
≔ @eq_refl (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S1)
  (@Const_func K (@CommRingFreydPresentation_cat R) T1)) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext
  td chainT) (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  walking_arrow_src);

// Retain the original whole last projection and its raw arrow.
symbol freyd_raw_native_row_last_whole_path [K : Cat] [R : τ CommRing]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  (chainS : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd))
  (chainT : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td))
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : τ (@= (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S0)
  (@Const_func K (@CommRingFreydPresentation_cat R) T0)) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext
  td chainT) (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  walking_arrow_tgt) (@Const_transf K (@CommRingFreydPresentation_cat R) S0 T0 (@comm_ring_freyd_hom_class R S0
  T0 f0)))
≔ @eq_refl (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S0)
  (@Const_func K (@CommRingFreydPresentation_cat R) T0)) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext
  td chainT) (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  walking_arrow_tgt);
