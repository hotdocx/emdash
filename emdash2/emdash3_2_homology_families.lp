/* Whole homology of an already coherent family of zero-arrow diagrams.
   The input h is a transformation of whole diagram-valued functors, not a
   function assigning isolated square proofs to objects of the base. */
require open emdash.emdash3_2_kernel_adjunction_presentations;
require open emdash.emdash3_2_cokernel_adjunction_presentations;

symbol kernel_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (Functor B C)
≔ @comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) D;

symbol kernel_family_unit_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  : τ (@Transf B C A
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)))
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B C C A (@id_func C)
      (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C
        (@kernel_presentation_func C S t T W P) (@terminal_arrow_diagram_func C t T)))
    (@unit_adj_transf C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P)
      (@kernel_presentation_adjunction C S t T W P));

symbol kernel_family_action_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A))
      (@kernel_family_func B C S t T W P D))
≔ @fapp0 _ _ (@comp_cat_cov_fapp1_func B (Functor_cat WalkingArrow_cat C) C
      (@kernel_presentation_func C S t T W P)
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D) h;

// beta = (K h) ∘ (eta A), with associativity handled by existing usability.
symbol kernel_family_boundary_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C A (@kernel_family_func B C S t T W P D))
≔ @comp_fapp0 (Functor_cat B C) A _ (@kernel_family_func B C S t T W P D)
    (@kernel_family_action_transf B C S t T W P A D h)
    (@kernel_family_unit_transf B C S t T W P A);

symbol kernel_family_boundary_diagram_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func B C A (@kernel_family_func B C S t T W P D)
    (@kernel_family_boundary_transf B C S t T W P A D h);

// H = Q applied to the whole boundary diagram family. No new primitive H.
symbol homology_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B C)
≔ @comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_presentation_func C S t T0 V Q)
    (@kernel_family_boundary_diagram_func B C S t T W P A D h);

// Whole observation of the introduced boundary really returns beta.
