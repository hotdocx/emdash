/* Point observations derived from the original whole row restriction. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_families;
require open emdash.emdash3_2_one_cat_zero_cone_row_families;
require open emdash.emdash3_2_whiskering_component_paths;

// Retain the original matrix morphism class after whole restriction and evaluation.
symbol freyd_native_row_incoming_at_path [K : Cat] [R : τ CommRing] [A B D : τ (@CommRingPresentation R)]
 (i : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
 (chain : τ (@CommRingFreydChainPair R A B D i d)) (x : τ (Obj K))
 : τ (@= (Hom (@CommRingFreydPresentation_cat R) A B) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R A B D i d chain))
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_src)
  x (@one_cat_zero_cone_row_family_incoming K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain))) (@comm_ring_freyd_hom_class R A B i))
≔ @eq_trans _ _ _ _
 (@eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_src)) (Hom
  (@CommRingFreydPresentation_cat R) A B)
  (λ e : τ (@Transf K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_source_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain)) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_src)), @tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_source_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R
  A B D i d chain)) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R A
  B D i d chain) walking_arrow_src) x e) _ _
  (@one_cat_zero_cone_row_incoming_whisker_path K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain)))
 (@prewhisker_component_path K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R)
  (@freyd_raw_native_row_family K R A B D i d chain) (@zero_arrow_cone_first_func
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
  (@zero_arrow_cone_vertex_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) walking_arrow_src) (@zero_arrow_family_incoming_transf
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@zero_arrow_cone_diagram_func
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
  (@zero_arrow_cone_universal_transf (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_cat_is_one_cat
  R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))) x);

// Retain the original matrix morphism class after whole restriction and evaluation.
symbol freyd_native_row_outgoing_at_path [K : Cat] [R : τ CommRing] [A B D : τ (@CommRingPresentation R)]
 (i : τ (@CommRingPresentationMorphism R A B)) (d : τ (@CommRingPresentationMorphism R B D))
 (chain : τ (@CommRingFreydChainPair R A B D i d)) (x : τ (Obj K))
 : τ (@= (Hom (@CommRingFreydPresentation_cat R) B D) (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_src)
  (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_tgt)
  x (@zero_cone_row_family_outgoing K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R A B D i d chain)))
  (@comm_ring_freyd_hom_class R B D d))
≔ @eq_trans _ _ _ _
 (@eq_ap (@Transf K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_src) (@zero_cone_row_family_vertex_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_tgt)) (Hom
  (@CommRingFreydPresentation_cat R) B D)
  (λ e : τ (@Transf K (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_src) (@zero_cone_row_family_vertex_func
  K (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain) walking_arrow_tgt)), @tapp0_fapp0 K
  (@CommRingFreydPresentation_cat R) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R
  A B D i d chain) walking_arrow_src) (@zero_cone_row_family_vertex_func K (@CommRingFreydPresentation_cat
  R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_raw_native_row_family K R
  A B D i d chain) walking_arrow_tgt) x e) _ _
  (@one_cat_zero_cone_row_outgoing_whisker_path K (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_raw_native_row_family K R A B D i d chain)))
 (@prewhisker_component_path K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R)
  (@freyd_raw_native_row_family K R A B D i d chain) (@zero_arrow_cone_vertex_func
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  walking_arrow_src) (@zero_arrow_cone_vertex_func (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) walking_arrow_tgt)
  (@zero_arrow_cone_differential_transf (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@comm_ring_freyd_terminal_zero R)) x);
