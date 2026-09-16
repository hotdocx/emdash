/* Native boundary and raw input observations of the original whole adjunction.
   The boundary is K(h) ∘ η and the pair observes h itself. No selected
   universal record or former homology algorithm is a dependency. */
require open emdash.emdash3_2_chain_pair_data;
require open emdash.emdash3_2_zero_arrow_diagram_observations;
require open emdash.emdash3_2_kernel_cokernel_adjunction_observations;

// Point of the existing whole transpose formula K(h) ∘ η.
symbol kernel_adjunction_semantic_boundary [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (Hom C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d))
≔ @fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d)) (@adjunction_transpose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X d) h;

// Derived observation using the existing whole mate/semantic comparison.
symbol kernel_adjunction_semantic_boundary_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@comp_fapp0 C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 _ _ _ _ d (@kernel_adjunction_inclusion C S t T P)) (@kernel_adjunction_semantic_boundary C S t T P X d h))
      (@terminal_arrow_test_incoming C t T X d h))
≔ @eq_trans (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ _ _
    (@eq_sym _ _ _
      (@eq_ap (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d))) (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
        (λ L : τ (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d))),
          @comp_fapp0 C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 _ _ _ _ d (@kernel_adjunction_inclusion C S t T P)) (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d)) L h))
        (@kernel_adjunction_lift_func C S t T P X d) (@adjunction_transpose_semantic_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) X d)
        (@adjunction_transpose_semantic_path C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
          (@kernel_adjunction_evidence C S t T P) X d)))
    (@eq_sym _ _ _ (@kernel_adjunction_unlift_source_path C S t T P X d
      (@fapp0 (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d) (Hom_cat C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d)) (@kernel_adjunction_lift_func C S t T P X d) h)));

// Unchanged observation of the actual input transformation.
symbol homology_family_pair [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B))
  : τ (@ComputationalChainPair C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt))
≔ @computational_chain_pair_intro C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@terminal_arrow_test_incoming C t T (@fapp0 B C A b) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D b h)) (@terminal_arrow_test_outgoing C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
    (@terminal_arrow_test_chain_path C S t T (@fapp0 B C A b) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D b h));
