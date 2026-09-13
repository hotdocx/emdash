/* Derived component equations from whole adjunction universality.
   Operations remain the native whole mate functors, not chosen test factors.
   The existing strict component theorem governs the zero observations;
   ordinary raw-input consumers retain an explicit OneCat profile. */
require open emdash.emdash3_2_kernel_cokernel_adjunction_mates;
require open emdash.emdash3_2_zero_arrow_diagram_observations;

// Source evaluation of the inverse kernel mate is k∘f.
symbol kernel_adjunction_unlift_source_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) d)))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@terminal_arrow_test_incoming C t T X d (@fapp0 _ _ (@kernel_adjunction_unlift_func C S t T P X d) f))
      (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T P)) f))
≔ @eq_ap
    (Functor (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
    (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (λ L : τ (Functor (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d)),
      @tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d walking_arrow_src (@fapp0 _ _ L f))
    (@adjunction_untranspose_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X d) (@adjunction_untranspose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X d)
    (@adjunction_untranspose_semantic_path C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X d);

// Cancel the whole mate pair, then observe its source component.
symbol kernel_adjunction_lift_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T P))
      (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T P X d) h))
    (@terminal_arrow_test_incoming C t T X d h))
≔ @eq_sym _ _ _ (@kernel_adjunction_unlift_source_path C S t T P X d
    (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T P X d) h));

// Target evaluation of the inverse cokernel mate is f∘q.
symbol cokernel_adjunction_uncolift_target_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (f : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) d) X))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
    (@initial_arrow_test_outgoing C t T X d
      (@fapp0 _ _ (@cokernel_adjunction_uncolift_func C S t T P X d) f))
    (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) d) X f (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T P))))
≔ @eq_ap (Functor (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))) (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
    (λ L : τ (Functor (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) d) X) (Hom_cat (Functor_cat WalkingArrow_cat C) d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))),
      @tapp0_fapp0 WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X) walking_arrow_tgt (@fapp0 _ _ L f))
    _ _ (@adjunction_transpose_semantic_path (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T P) (@initial_arrow_diagram_func C t T)
      (@cokernel_adjunction_evidence C S t T P) d X);

// Cancel the whole mate pair, then observe its target component.
symbol cokernel_adjunction_colift_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
    (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) d) X
      (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T P X d) h) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T P)))
    (@initial_arrow_test_outgoing C t T X d h))
≔ @eq_sym _ _ _ (@cokernel_adjunction_uncolift_target_path C S t T P X d
    (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T P X d) h));

// The actual counit supplies the zero equation.
symbol kernel_adjunction_annihilation [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Hom C (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
    (@comp_fapp0 C _ _ _ (@terminal_arrow_test_outgoing C d)
      (@tapp0_fapp0 _ _ _ _ d (@kernel_adjunction_inclusion C S t T P)))
    (@preadditive_hom_zero C S (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))
≔ @terminal_arrow_test_chain_path C S t T
    (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d) d
    (@tapp0_fapp0 _ _ _ _ d
      (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)));

// The actual unit supplies the zero equation.
symbol cokernel_adjunction_annihilation [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@CokernelAdjunctionStructure C S t T)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 _ _ (@cokernel_adjunction_func C S t T P) d))
      (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_adjunction_func C S t T P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_adjunction_projection C S t T P)) (@terminal_arrow_test_outgoing C d))
      (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 _ _ (@cokernel_adjunction_func C S t T P) d)))
≔ @initial_arrow_test_chain_path C S t T (@fapp0 _ _ (@cokernel_adjunction_func C S t T P) d) d
    (@tapp0_fapp0 _ _ _ _ d
      (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C
        (@cokernel_adjunction_func C S t T P) (@initial_arrow_diagram_func C t T)
        (@cokernel_adjunction_evidence C S t T P)));
