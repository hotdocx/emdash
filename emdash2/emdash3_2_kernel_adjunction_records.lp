/* Universal kernel records derived from whole adjunction observations.
   Object and structural arrow are literal whole operations. The factor-space
   proof reuses the selected interpretation, with the computational centre
   explicitly fixed to the mate operation. No object/map transport, new
   primitive, rewrite or unification rule is introduced. Proof transport is
   confined to universality; its computational centre is explicitly installed. */
/* Whole K object/inclusion with the original selected lift as a mate. */
require open emdash.emdash3_2_kernel_adjunction_unmate_paths;

symbol kernel_record_frame [C : Cat] (A : τ (Obj C)) : Grpd
≔ @Σ_ (Obj C) (λ K : τ (Obj C), Hom C K A);

symbol kernel_record_frame_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (@kernel_record_frame C (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (@Struct_sigma (Obj C) (λ K : τ (Obj C), Hom C K (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)))
    (@Struct_sigma (Obj C) (λ K : τ (Obj C), Hom C K (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@kernel_presentation_selected_object C S W d)
      (@computational_kernel_morphism C S
        (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
        (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d))))
≔ @eq_refl (@kernel_record_frame C (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (@Struct_sigma (Obj C) (λ K : τ (Obj C), Hom C K (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)));

symbol kernel_record_lift [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C))
  (e : τ (@WeakKernelAnnihilator C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) X))
  : τ (Hom C X (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d))
≔ @fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d)
    (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d)
      (@kernel_presentation_test_lift C S W X d e));

symbol kernel_record_lift_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C))
  (e : τ (@WeakKernelAnnihilator C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) X))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (@comp_fapp0 C X (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_src)
      (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P))
      (@kernel_record_lift C S t T W P d X e))
    (@weak_kernel_annihilator_arrow C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) X e))
≔ @eq_trans (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ _ _
    (@eq_sym _ _ _ (@kernel_presentation_unlift_source_semantic_path C S t T W P X d
      (@kernel_record_lift C S t T W P d X e)))
    (@kernel_presentation_unlift_lift_source_path C S t T W P X d e);

/* Universal proof over K[d], with an explicitly chosen operational centre. */

symbol kernel_record_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C))
  (e : τ (@WeakKernelAnnihilator C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) X))
  : τ (@KernelFactorSpace C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d)
    (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
    (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)) X e)
≔ @Struct_sigma
    (Hom C X (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d))
    (λ u : τ (Hom C X (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)),
      @= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
        (@comp_fapp0 C X (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
          (@fapp0 WalkingArrow_cat C d walking_arrow_src)
          (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)) u)
        (@weak_kernel_annihilator_arrow C S
          (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) X e))
    (@kernel_record_lift C S t T W P d X e)
    (@kernel_record_lift_reconstruction C S t T W P d X e);

symbol kernel_record_universal [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C))
  (e : τ (@WeakKernelAnnihilator C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) X))
  : τ (IsContr (@KernelFactorSpace C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d)
    (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
    (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)) X e))
≔ @is_contr_recenter
    (@KernelFactorSpace C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d)
      (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)) X e)
    (@ind_eq (@kernel_record_frame C (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@Struct_sigma (Obj C) (λ K : τ (Obj C), Hom C K (@fapp0 WalkingArrow_cat C d walking_arrow_src))
        (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
        (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)))
      (@Struct_sigma (Obj C) (λ K : τ (Obj C), Hom C K (@fapp0 WalkingArrow_cat C d walking_arrow_src))
        (@kernel_presentation_selected_object C S W d)
        (@computational_kernel_morphism C S
          (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d)))
      (@kernel_record_frame_path C S t T W P d)
      (λ frame : τ (@kernel_record_frame C (@fapp0 WalkingArrow_cat C d walking_arrow_src)),
        IsContr (@KernelFactorSpace C S
          (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (sigma_Fst frame) (sigma_Snd frame) X e))
      (@computational_kernel_factor_contr C S
        (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
        (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X e))
    (@kernel_record_factor C S t T W P d X e);

symbol kernel_record_annihilation [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Hom C (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
    (@comp_fapp0 C _ _ _ (@terminal_arrow_test_outgoing C d)
      (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P)))
    (@preadditive_hom_zero C S (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))
≔ @terminal_arrow_test_chain_path C S t T
    (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d) d
    (@tapp0_fapp0 _ _ _ _ d
      (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P)
        (@kernel_presentation_adjunction C S t T W P)));

symbol kernel_presentation_record [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@ComputationalKernel C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d))
≔ @computational_kernel_intro C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d)
    (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
    (@tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P))
    (@kernel_record_annihilation C S t T W P d)
    (@kernel_record_universal C S t T W P d);
