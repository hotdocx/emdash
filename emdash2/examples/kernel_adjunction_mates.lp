/* Independent selection and proof-payload controls. */
require open emdash.emdash3_2_kernel_adjunction_mates;

// Any valid annihilation proof for this same test arrow is accepted.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    d))
  (z : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (@comp_fapp0 C X _ _ (@terminal_arrow_test_outgoing C d) (@terminal_arrow_test_incoming C t T X d h)) (@preadditive_hom_zero C S X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))) ⊢
  @eq_refl (Hom C X (@kernel_presentation_selected_object C S W d)) (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h)
  : τ (@= (Hom C X (@kernel_presentation_selected_object C S W d)) (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h) (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X
      (@Struct_sigma (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (λ e : τ (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)), @= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (@comp_fapp0 C X _ _ (@terminal_arrow_test_outgoing C d) e) (@preadditive_hom_zero C S X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))) (@terminal_arrow_test_incoming C t T X d h) z)));

// A different test arrow is not accepted, even with a valid zero proof.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    d))
  (other : τ (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)))
  (z : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (@comp_fapp0 C X _ _ (@terminal_arrow_test_outgoing C d) other) (@preadditive_hom_zero C S X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))) ⊢
  @eq_refl (Hom C X (@kernel_presentation_selected_object C S W d)) (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h)
  : τ (@= (Hom C X (@kernel_presentation_selected_object C S W d)) (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h) (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X
      (@Struct_sigma (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (λ e : τ (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)), @= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (@comp_fapp0 C X _ _ (@terminal_arrow_test_outgoing C d) e) (@preadditive_hom_zero C S X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))) other z)));

// This interface does not install a runtime fold to the raw lift.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    d)) ⊢
  (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h) ≡ @kernel_presentation_lift_semantic C S t T W X d h;

// The original universal reconstruction remains an explicit defined proof.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    d)) ⊢ @kernel_presentation_lift_reconstruction C S t T W P X d h
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@comp_fapp0 C X _ _
        (@computational_kernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d)) (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h))
      (@terminal_arrow_test_incoming C t T X d h));
