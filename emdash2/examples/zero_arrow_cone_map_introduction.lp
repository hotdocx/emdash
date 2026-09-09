/* Constructor observations of a derived native map; no new square field. */
require open emdash.emdash3_2_zero_arrow_cone_map_introduction;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 A1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
  (h0 : τ (Hom C A0 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d0)))
  (h1 : τ (Hom C A1 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d1)))
  (a : τ (Hom C A0 A1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (p : τ (@= (Hom C A0 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d1))
    (@comp_fapp0 C _ _ _
      (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 b) h0)
    (@comp_fapp0 C _ _ _ h1 a))) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@zero_arrow_cone_obj C t T A0 d0
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A0 d0) h0)) (@zero_arrow_cone_obj C t T A1 d1
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A1 d1) h1)) (@zero_cone_map_from_lifts C S t T W P A0 A1 d0 d1 h0 h1 a b p) ≡ a;
assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 A1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
  (h0 : τ (Hom C A0 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d0)))
  (h1 : τ (Hom C A1 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d1)))
  (a : τ (Hom C A0 A1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (p : τ (@= (Hom C A0 (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d1))
    (@comp_fapp0 C _ _ _
      (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 b) h0)
    (@comp_fapp0 C _ _ _ h1 a))) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T A0 d0
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A0 d0) h0)) (@zero_arrow_cone_obj C t T A1 d1
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A1 d1) h1)) (@zero_cone_map_from_lifts C S t T W P A0 A1 d0 d1 h0 h1 a b p) ≡ b;
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
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
  (other : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A0 d0
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A0 d0) h0)) (@zero_arrow_cone_obj C t T A1 d1
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A1 d1) h1)))) ⊢
  eq_refl (@zero_cone_map_from_lifts C S t T W P A0 A1 d0 d1 h0 h1 a b p) : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A0 d0
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A0 d0) h0)) (@zero_arrow_cone_obj C t T A1 d1
      (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A1 d1) h1))) (@zero_cone_map_from_lifts C S t T W P A0 A1 d0 d1 h0 h1 a b p) other);
