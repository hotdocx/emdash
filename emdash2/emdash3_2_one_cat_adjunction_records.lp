/* Ordinary universal records derived from whole adjunctions.
   The object, structural map and factor centres are the actual whole
   operations. Native square/diagram equality derives cancellation; the
   existing set-valued HFiber theorem derives each contraction. There is no
   selected W/V input or transfer of a selected universal record. */
require open emdash.emdash3_2_one_cat_adjunction_cancellation;
require open emdash.emdash3_2_one_cat_zero_diagram_inputs;
require open emdash.emdash3_2_hfiber_cancellation;
require open emdash.emdash3_2_kernels_cokernels;

// Derived record view: the centre is the native mate, with its reconstruction.
protected symbol kernel_adjunction_record_factor [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C)) (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@KernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U)) X e)
≔ (λ h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d),
      @Struct_sigma (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (λ u : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)), @= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U)) u) (@terminal_arrow_test_incoming C t T X d h))
        (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T U X d) h) (@kernel_adjunction_lift_reconstruction C S t T U X d h))
    (@terminal_diagram_test_transf C S C1 t T X d (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@weak_kernel_annihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e));

// All-test contraction is derived; it is not a supplied factor dictionary.
symbol kernel_adjunction_record [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C))
  : τ (@ComputationalKernel C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d))
≔ @computational_kernel_intro C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U))
    (@kernel_adjunction_annihilation C S t T U d)
    (λ X : τ (Obj C), λ e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X),
      @hfiber_contr_from_cancellation (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
        (@preadditive_hom_is_set C S X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
        (λ u : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)), (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U)) u))
        (@kernel_adjunction_cancel_path C S C1 t T U X d) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)
        (@kernel_adjunction_record_factor C S C1 t T U d X e));

// Derived record view: the centre is the native mate, with its reconstruction.
protected symbol cokernel_adjunction_record_factor [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@CokernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U)) X e)
≔ (λ h : τ (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)),
      @Struct_sigma (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (λ u : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X), @= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X u (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U))) (@initial_arrow_test_outgoing C t T X d h))
        (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T U X d) h) (@cokernel_adjunction_colift_reconstruction C S t T U X d h))
    (@initial_diagram_test_transf C S C1 t T X d (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@cokernel_coannihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e));

// All-test contraction is derived; it is not a supplied factor dictionary.
symbol cokernel_adjunction_record [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C))
  : τ (@ComputationalCokernel C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d))
≔ @computational_cokernel_intro C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U))
    (@cokernel_adjunction_annihilation C S t T U d)
    (λ X : τ (Obj C), λ e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X),
      @hfiber_contr_from_cancellation (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
        (@preadditive_hom_is_set C S (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
        (λ u : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X), (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X u (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U))))
        (@cokernel_adjunction_cancel_path C S C1 t T U X d) (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)
        (@cokernel_adjunction_record_factor C S C1 t T U d X e));
