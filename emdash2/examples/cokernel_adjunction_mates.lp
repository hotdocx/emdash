/* Independent selection and proof-payload controls. */
require open emdash.emdash3_2_cokernel_adjunction_mates;

// Any valid annihilation proof for this same test arrow is accepted.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalCokernels C S))
  (P : τ (@CokernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
  (z : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) X) (@comp_fapp0 C _ _ X (@initial_arrow_test_outgoing C t T X d h) (@terminal_arrow_test_outgoing C d)) (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) X))) ⊢
  @eq_refl (Hom C (@cokernel_presentation_selected_object C S W d) X) (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h)
  : τ (@= (Hom C (@cokernel_presentation_selected_object C S W d) X) (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h) (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X
      (@Struct_sigma (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) (λ e : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X), @= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) X) (@comp_fapp0 C _ _ X e (@terminal_arrow_test_outgoing C d)) (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) X)) (@initial_arrow_test_outgoing C t T X d h) z)));

// A different test arrow is not accepted, even with a valid zero proof.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalCokernels C S))
  (P : τ (@CokernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
  (other : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X))
  (z : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) X) (@comp_fapp0 C _ _ X other (@terminal_arrow_test_outgoing C d)) (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) X))) ⊢
  @eq_refl (Hom C (@cokernel_presentation_selected_object C S W d) X) (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h)
  : τ (@= (Hom C (@cokernel_presentation_selected_object C S W d) X) (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h) (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X
      (@Struct_sigma (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) (λ e : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X), @= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) X) (@comp_fapp0 C _ _ X e (@terminal_arrow_test_outgoing C d)) (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) X)) other z)));

// This interface does not install a runtime fold to the raw lift.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalCokernels C S))
  (P : τ (@CokernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))) ⊢
  (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h) ≡ @cokernel_presentation_colift_semantic C S t T W d X h;

// The original universal reconstruction remains an explicit defined proof.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalCokernels C S))
  (P : τ (@CokernelPresentation C S t T W))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))) ⊢ @cokernel_presentation_colift_reconstruction C S t T W P d X h
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
      (@comp_fapp0 C _ _ X (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h)
        (@computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d)))
      (@initial_arrow_test_outgoing C t T X d h));
