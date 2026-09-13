/* Legacy annihilator-package views of the independent diagram observations.
   These definitions package existing arrows and paths; no universal
   selection is used to obtain those observations. */
require open emdash.emdash3_2_zero_arrow_diagram_observations;
require open emdash.emdash3_2_kernels_cokernels;

symbol terminal_arrow_kernel_test [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (@WeakKernelAnnihilator C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) A)
≔ @Struct_sigma (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (λ e : τ (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_src)),
      @= (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
        (@comp_fapp0 C A _ _ (@terminal_arrow_test_outgoing C d) e)
        (@preadditive_hom_zero C S A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))
    (@terminal_arrow_test_incoming C t T A d h)
    (@terminal_arrow_test_chain_path C S t T A d h);

symbol initial_arrow_cokernel_test [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (@CokernelCoannihilator C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) A)
≔ @Struct_sigma (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) A)
    (λ e : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) A),
      @= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) A)
        (@comp_fapp0 C _ _ A e (@terminal_arrow_test_outgoing C d))
        (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) A))
    (@initial_arrow_test_outgoing C t T A d h)
    (@initial_arrow_test_chain_path C S t T A d h);
