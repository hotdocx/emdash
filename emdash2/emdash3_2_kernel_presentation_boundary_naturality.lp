/* Derived compatibility after the ORIGINAL target inclusion. */
require open emdash.emdash3_2_kernel_presentation_inclusion_properties;

symbol kernel_presentation_boundary_after_inclusion_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [X0 X1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
  (e0 : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d0) X0))
  (e1 : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d1) X1))
  (a : τ (Hom C X0 X1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (p : τ (@= (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src))
    (@comp_fapp0 C X0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src b) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d0) X0 e0))
    (@comp_fapp0 C X0 X1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d1) X1 e1) a)))
  : τ (@= (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src))
      (@comp_fapp0 C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d1 (@kernel_presentation_inclusion C S t T W P)) (@comp_fapp0 C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0 d1 b) (@kernel_presentation_test_lift C S W X0 d0 e0)))
      (@comp_fapp0 C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d1 (@kernel_presentation_inclusion C S t T W P)) (@comp_fapp0 C X0 X1 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@kernel_presentation_test_lift C S W X1 d1 e1) a)))
≔ (@eq_trans (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) _ _ _
    (@comp_assoc C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d1 (@kernel_presentation_inclusion C S t T W P)) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0 d1 b) (@kernel_presentation_test_lift C S W X0 d0 e0))
    (@eq_trans (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) _ _ _
    (@eq_ap (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src))
      (λ v : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)), (@comp_fapp0 C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) v (@kernel_presentation_test_lift C S W X0 d0 e0))) _ _
      (@eq_sym _ _ _ (@strict_component_naturality_path (Functor_cat WalkingArrow_cat C) C
        (@kernel_presentation_func C S t T W P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@kernel_presentation_inclusion C S t T W P) d0 d1 b)))
    (@eq_trans (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) _ _ _
    (@eq_sym _ _ _ (@comp_assoc C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src b) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d0 (@kernel_presentation_inclusion C S t T W P)) (@kernel_presentation_test_lift C S W X0 d0 e0)))
    (@eq_trans (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) _ _ _
    (@eq_ap (Hom C X0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src)) (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src))
      (λ v : τ (Hom C X0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src)), (@comp_fapp0 C X0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src b) v)) _ _
      (@kernel_presentation_test_lift_path C S t T W P X0 d0 e0))
    (@eq_trans (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) _ _ _
    p
    (@eq_trans (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) _ _ _
    (@eq_ap (Hom C X1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)) (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src))
      (λ v : τ (Hom C X1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src)), (@comp_fapp0 C X0 X1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) v a)) _ _
      (@eq_sym _ _ _ (@kernel_presentation_test_lift_path C S t T W P X1 d1 e1)))
    (@eq_sym _ _ _ (@comp_assoc C X0 X1 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d1 (@kernel_presentation_inclusion C S t T W P)) (@kernel_presentation_test_lift C S W X1 d1 e1) a))))))));

symbol kernel_presentation_boundary_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [X0 X1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
  (e0 : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d0) X0))
  (e1 : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d1) X1))
  (a : τ (Hom C X0 X1)) (b : τ (@Transf WalkingArrow_cat C d0 d1))
  (p : τ (@= (Hom C X0 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src))
    (@comp_fapp0 C X0 (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src b) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d0) X0 e0))
    (@comp_fapp0 C X0 X1 (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt) (@terminal_arrow_test_outgoing C d1) X1 e1) a)))
  : τ (@= (Hom C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1)) (@comp_fapp0 C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0 d1 b) (@kernel_presentation_test_lift C S W X0 d0 e0)) (@comp_fapp0 C X0 X1 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@kernel_presentation_test_lift C S W X1 d1 e1) a))
≔ (@kernel_presentation_inclusion_monic C S t T W P d1)
    X0 (@comp_fapp0 C X0 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0 d1 b) (@kernel_presentation_test_lift C S W X0 d0 e0)) (@comp_fapp0 C X0 X1 (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d1) (@kernel_presentation_test_lift C S W X1 d1 e1) a)
    (@kernel_presentation_boundary_after_inclusion_path C S t T W P X0 X1 d0 d1 e0 e1 a b p);
