require open emdash.emdash3_2_one_cat_arrow_diagrams;
require open emdash.emdash3_2_chain_pair_diagrams;
require open emdash.emdash3_2_chain_pair_cubical_maps;

/* Retain whole action in the original equality-valued raw-map parameter. */

symbol chain_pair_outgoing_diagram_map_func
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor
      (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
      (Hom_cat (Functor_cat WalkingArrow_cat C)
        (@chain_pair_outgoing_diagram C S A0 B0 D0 p0)
        (@chain_pair_outgoing_diagram C S A1 B1 D1 p1)))
≔ @comp_cat_fapp0 _ _ _
    (@fapp1_func (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1)
      (@lax_edge C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0))
      (@lax_edge C B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1)))
    (@comp_cat_fapp0 _ _ _
      (@Product_projR_func
        (Hom_cat (@LaxArrow_cat C)
          (@lax_edge C A0 B0 (@computational_chain_pair_dnext C S A0 B0 D0 p0))
          (@lax_edge C A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1)))
        (Hom_cat (@LaxArrow_cat C)
          (@lax_edge C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0))
          (@lax_edge C B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1))))
      (@computational_chain_pair_map_cubical_boundary_func
        C S A0 B0 D0 A1 B1 D1 p0 p1));

/* Existing factor data realized as an ACTUAL arrow-diagram transformation. */

symbol chain_pair_outgoing_diagram_map [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@Transf WalkingArrow_cat C
      (@chain_pair_outgoing_diagram C S A0 B0 D0 p0)
      (@chain_pair_outgoing_diagram C S A1 B1 D1 p1))
≔ @fapp0 _ _ (@chain_pair_outgoing_diagram_map_func C S C1 A0 B0 D0 A1 B1 D1 p0 p1) m;
