require open emdash.emdash3_2_adjunction_untranspose_naturality;
require open emdash.emdash3_2_chain_pair_zero_cones;

/* Auxiliary native introduction; the comparison cell is derived, not supplied.
   The primary raw-map consumer must derive p from its existing data. */

symbol zero_cone_map_from_lifts
  [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 A1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
  (h0 : τ (Hom C A0 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d0)))
  (h1 : τ (Hom C A1 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d1)))
  (a : τ (Hom C A0 A1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (p : τ (@= (Hom C A0 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d1))
    (@comp_fapp0 C _ _ _
      (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 b) h0)
    (@comp_fapp0 C _ _ _ h1 a)))
  : τ (Hom (@ZeroArrowCone_cat C t T)
      (@zero_arrow_cone_obj C t T A0 d0
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A0 d0) h0))
      (@zero_arrow_cone_obj C t T A1 d1
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A1 d1) h1)))
≔ Struct_sigma a (Struct_sigma b
    (@path_to_hom
      (Hom_cat (Functor_cat WalkingArrow_cat C)
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d1)
      (@comp_fapp0 (Functor_cat WalkingArrow_cat C) _ _ _ b
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A0 d0) h0))
      (@comp_fapp0 (Functor_cat WalkingArrow_cat C) _ _ _
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A1 d1) h1)
        (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0 A1 a))
      (@untranspose_square_path C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P)
        (@kernel_presentation_adjunction C S t T W P) A0 A1 d0 d1 a b h0 h1 p)));
