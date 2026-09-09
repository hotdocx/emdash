/* Reusable compatibility proofs; not the implementation of whole H. */
require open emdash.emdash3_2_kernel_adjunction_unmates;

// The standard counit formula, observed at the walking-arrow source.
symbol kernel_presentation_unlift_source_semantic_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@terminal_arrow_test_incoming C t T X d (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d) f))
      (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_presentation_inclusion C S t T W P)) f))
≔ @eq_ap
    (Functor (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
    (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (λ L : τ (Functor (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d)),
      @tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d walking_arrow_src (@fapp0 _ _ L f))
    (@adjunction_untranspose_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d) (@adjunction_untranspose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d)
    (@adjunction_untranspose_semantic_path C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d);

// Package the common-middle choice together with both arrows.
symbol kernel_presentation_unlift_composition_input_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)))
  : τ (@= (`Σ_ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@Struct_sigma (Obj C) (λ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)
      (@Product_pair_grpd (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_presentation_inclusion C S t T W P)) f)) (@Struct_sigma (Obj C) (λ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@kernel_presentation_selected_object C S W d)
      (@Product_pair_grpd (Hom C (@kernel_presentation_selected_object C S W d) (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X (@kernel_presentation_selected_object C S W d)) (@computational_kernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d)) f)))
≔ @eq_refl (`Σ_ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@Struct_sigma (Obj C) (λ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)
      (@Product_pair_grpd (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_presentation_inclusion C S t T W P)) f));

// The semantic side uses the ORIGINAL selected middle endpoint.
symbol kernel_presentation_unlift_source_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@terminal_arrow_test_incoming C t T X d
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d) f))
      (@comp_fapp0 C X (@kernel_presentation_selected_object C S W d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@computational_kernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d)) f))
≔ @eq_trans (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ _ _
    (@kernel_presentation_unlift_source_semantic_path C S t T W P X d f)
    (@eq_ap (`Σ_ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (λ z : τ (`Σ_ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)), @comp_fapp0 C X (sigma_Fst z) (@fapp0 WalkingArrow_cat C d walking_arrow_src)
        (sigma_Fst (sigma_Snd z)) (sigma_Snd (sigma_Snd z)))
      (@Struct_sigma (Obj C) (λ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)
      (@Product_pair_grpd (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_presentation_inclusion C S t T W P)) f)) (@Struct_sigma (Obj C) (λ M : τ (Obj C), @Product_grpd (Hom C M (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X M)) (@kernel_presentation_selected_object C S W d)
      (@Product_pair_grpd (Hom C (@kernel_presentation_selected_object C S W d) (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (Hom C X (@kernel_presentation_selected_object C S W d)) (@computational_kernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d)) f))
      (@kernel_presentation_unlift_composition_input_path C S t T W P X d f));

/* Reconstruct at the retained diagram-selected kernel before specializing. */
symbol kernel_presentation_unlift_lift_source_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@terminal_arrow_test_incoming C t T X d
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d) (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X e)))
      (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))
≔ @eq_trans (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ _ _
    (@kernel_presentation_unlift_source_path C S t T W P X d (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X e))
    (@computational_kernel_lift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X e);

/* Semantic unit formula after an inverse mate, without another unifier. */
symbol kernel_presentation_semantic_unlift_beta_path [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)))
  : τ (@= (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (@adjunction_transpose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d) (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d) f)) f)
≔ @eq_sym (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) f (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (@adjunction_transpose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d) (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d) f))
    (@eq_ap (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d))) (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d))
      (λ L : τ (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d))), @fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) L (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P X d) f))
      (@adjunction_transpose_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d) (@adjunction_transpose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d)
      (@adjunction_transpose_semantic_path C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d));
