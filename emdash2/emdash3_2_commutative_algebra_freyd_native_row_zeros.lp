/* The original raw middle-column agreement gives the actual whole row-window zero. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_paths;
require open emdash.emdash3_2_one_cat_constant_chain_zeros;
require open emdash.emdash3_2_commutative_algebra_freyd_additive;

symbol freyd_raw_native_row_middle_zero [K : Cat] [R : τ CommRing]
  (Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)))
  [S2 S1 S0 M2 M1 M0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [se : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [me : τ (@CommRingPresentationMorphism R M2 M1)]
  [md : τ (@CommRingPresentationMorphism R M1 M0)]
  [te : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [a0 : τ (@CommRingPresentationMorphism R S2 M2)]
  [b0 : τ (@CommRingPresentationMorphism R S1 M1)]
  [c0 : τ (@CommRingPresentationMorphism R S0 M0)]
  [a1 : τ (@CommRingPresentationMorphism R M2 T2)]
  [b1 : τ (@CommRingPresentationMorphism R M1 T1)]
  [c1 : τ (@CommRingPresentationMorphism R M0 T0)]
  (sc : τ (@CommRingFreydChainPair R S2 S1 S0 se sd))
  (mc : τ (@CommRingFreydChainPair R M2 M1 M0 me md))
  (tc : τ (@CommRingFreydChainPair R T2 T1 T0 te td))
  (f : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 M2 M1 M0 se sd me md a0 b0 c0))
  (g : τ (@CommRingFreydHomologyChainMap R M2 M1 M0 T2 T1 T0 me md te td a1 b1 c1))
  (vertical_zero : τ (@CommRingFreydChainPair R S1 M1 T1 b0 b1))
  : τ (@= (@Transf K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) walking_arrow_src)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te
  td tc) walking_arrow_src)) (@comp_fapp0 (Functor_cat K (@CommRingFreydPresentation_cat R))
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) walking_arrow_src) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src)
  (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R M2 M1 M0 me
  md mc) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) (@freyd_raw_native_row_map K R M2 M1 M0 T2 T1 T0
  me md te td a1 b1 c1 mc tc g) walking_arrow_src) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc)
  (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) (@freyd_raw_native_row_map K R S2 S1 S0 M2 M1 M0 se sd me
  md a0 b0 c0 sc mc f) walking_arrow_src)) (@zero_arrow_family_zero_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Z
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src)))
≔ @eq_trans (@Transf K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) walking_arrow_src)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te
  td tc) walking_arrow_src)) (@comp_fapp0 (Functor_cat K (@CommRingFreydPresentation_cat R))
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) walking_arrow_src) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src)
  (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R M2 M1 M0 me
  md mc) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) (@freyd_raw_native_row_map K R M2 M1 M0 T2 T1 T0
  me md te td a1 b1 c1 mc tc g) walking_arrow_src) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc)
  (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) (@freyd_raw_native_row_map K R S2 S1 S0 M2 M1 M0 se sd me
  md a0 b0 c0 sc mc f) walking_arrow_src)) (@comp_fapp0 (Functor_cat K (@CommRingFreydPresentation_cat R))
  (@Const_func K (@CommRingFreydPresentation_cat R) S1) (@Const_func K (@CommRingFreydPresentation_cat R) M1)
  (@Const_func K (@CommRingFreydPresentation_cat R) T1) (@Const_transf K (@CommRingFreydPresentation_cat R) M1
  T1 (@comm_ring_freyd_hom_class R M1 T1 b1)) (@Const_transf K (@CommRingFreydPresentation_cat R) S1 M1
  (@comm_ring_freyd_hom_class R S1 M1 b0))) (@zero_arrow_family_zero_transf K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Z
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src)) (@eq_trans (@Transf K
  (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src))
  (@comp_fapp0 (Functor_cat K (@CommRingFreydPresentation_cat R)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) walking_arrow_src)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R M2 M1 M0 me
  md mc) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R M2 M1 M0 me md mc)
  (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) (@freyd_raw_native_row_map K R M2 M1 M0 T2 T1 T0 me md te
  td a1 b1 c1 mc tc g) walking_arrow_src) (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) (@freyd_raw_native_row_family K R M2 M1 M0 me md mc)
  (@freyd_raw_native_row_map K R S2 S1 S0 M2 M1 M0 se sd me md a0 b0 c0 sc mc f) walking_arrow_src))
  (@comp_fapp0 (Functor_cat K (@CommRingFreydPresentation_cat R)) (@Const_func K (@CommRingFreydPresentation_cat
  R) S1) (@Const_func K (@CommRingFreydPresentation_cat R) M1) (@Const_func K (@CommRingFreydPresentation_cat R)
  T1) (@Const_transf K (@CommRingFreydPresentation_cat R) M1 T1 (@comm_ring_freyd_hom_class R M1 T1 b1))
  (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) (@freyd_raw_native_row_map K R S2 S1 S0 M2 M1 M0
  se sd me md a0 b0 c0 sc mc f) walking_arrow_src)) (@comp_fapp0 (Functor_cat K (@CommRingFreydPresentation_cat
  R)) (@Const_func K (@CommRingFreydPresentation_cat R) S1) (@Const_func K (@CommRingFreydPresentation_cat R)
  M1) (@Const_func K (@CommRingFreydPresentation_cat R) T1) (@Const_transf K (@CommRingFreydPresentation_cat R)
  M1 T1 (@comm_ring_freyd_hom_class R M1 T1 b1)) (@Const_transf K (@CommRingFreydPresentation_cat R) S1 M1
  (@comm_ring_freyd_hom_class R S1 M1 b0))) (@eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) M1) (@Const_func K (@CommRingFreydPresentation_cat R) T1)) (@Transf K
  (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src)) (λ h :
  τ (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) M1)
  (@Const_func K (@CommRingFreydPresentation_cat R) T1)), (@comp_fapp0 (Functor_cat K
  (@CommRingFreydPresentation_cat R)) (@Const_func K (@CommRingFreydPresentation_cat R) S1) (@Const_func K
  (@CommRingFreydPresentation_cat R) M1) (@Const_func K (@CommRingFreydPresentation_cat R) T1) h
  (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) (@freyd_raw_native_row_map K R S2 S1 S0 M2 M1 M0
  se sd me md a0 b0 c0 sc mc f) walking_arrow_src))) (@zero_cone_row_family_vertex_map K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R M2 M1 M0 me md mc)
  (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) (@freyd_raw_native_row_map K R M2 M1 M0 T2 T1 T0 me md te
  td a1 b1 c1 mc tc g) walking_arrow_src) (@Const_transf K (@CommRingFreydPresentation_cat R) M1 T1
  (@comm_ring_freyd_hom_class R M1 T1 b1)) (@freyd_raw_native_row_middle_whole_path K R M2 M1 M0 T2 T1 T0 me md
  te td a1 b1 c1 mc tc g)) (@eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K
  (@CommRingFreydPresentation_cat R) S1) (@Const_func K (@CommRingFreydPresentation_cat R) M1)) (@Transf K
  (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@freyd_raw_native_row_family K R S2 S1 S0 se sd sc) walking_arrow_src) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R T2 T1 T0 te td tc) walking_arrow_src)) (λ h :
  τ (@Transf K (@CommRingFreydPresentation_cat R) (@Const_func K (@CommRingFreydPresentation_cat R) S1)
  (@Const_func K (@CommRingFreydPresentation_cat R) M1)), (@comp_fapp0 (Functor_cat K
  (@CommRingFreydPresentation_cat R)) (@Const_func K (@CommRingFreydPresentation_cat R) S1) (@Const_func K
  (@CommRingFreydPresentation_cat R) M1) (@Const_func K (@CommRingFreydPresentation_cat R) T1) (@Const_transf K
  (@CommRingFreydPresentation_cat R) M1 T1 (@comm_ring_freyd_hom_class R M1 T1 b1)) h))
  (@zero_cone_row_family_vertex_map K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_raw_native_row_family K R S2 S1 S0 se
  sd sc) (@freyd_raw_native_row_family K R M2 M1 M0 me md mc) (@freyd_raw_native_row_map K R S2 S1 S0 M2 M1 M0
  se sd me md a0 b0 c0 sc mc f) walking_arrow_src) (@Const_transf K (@CommRingFreydPresentation_cat R) S1 M1
  (@comm_ring_freyd_hom_class R S1 M1 b0)) (@freyd_raw_native_row_middle_whole_path K R S2 S1 S0 M2 M1 M0 se sd
  me md a0 b0 c0 sc mc f))) (@one_cat_constant_chain_zero_path K (@CommRingFreydPresentation_cat R)
  (@additive_preadditive (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@additive_terminal_object (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) Z S1 M1
  T1 (@comm_ring_freyd_hom_class R S1 M1 b0) (@comm_ring_freyd_hom_class R M1 T1 b1) (@freyd_raw_chain_zero_path
  R S1 M1 T1 b0 b1 vertical_zero));
