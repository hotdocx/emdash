/* Selected-presentation adapters for the independent whole H-family.
   The semantic implementation lives in homology_adjunction_families; these
   signatures retain the original selected realization and its comparisons. */
require open emdash.emdash3_2_homology_adjunction_families;
require open emdash.emdash3_2_kernel_adjunction_presentations;
require open emdash.emdash3_2_cokernel_adjunction_presentations;

symbol kernel_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (Functor B C)
≔ @kernel_adjunction_family_func B C S t T
    (@kernel_presentation_structure C S t T W P) D;

symbol kernel_family_unit_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  : τ (@Transf B C A
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)))
≔ @kernel_adjunction_family_unit_transf B C S t T
    (@kernel_presentation_structure C S t T W P) A;

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
≔ @kernel_adjunction_family_action_transf B C S t T
    (@kernel_presentation_structure C S t T W P) A D h;

// beta = (K h) ∘ (eta A), with associativity handled by existing usability.
symbol kernel_family_boundary_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C A (@kernel_family_func B C S t T W P D))
≔ @kernel_adjunction_family_boundary_transf B C S t T
    (@kernel_presentation_structure C S t T W P) A D h;

symbol kernel_family_boundary_diagram_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @kernel_adjunction_family_boundary_diagram_func B C S t T
    (@kernel_presentation_structure C S t T W P) A D h;

// H = Q applied to the whole boundary diagram family. No new primitive H.
symbol homology_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B C)
≔ @homology_adjunction_family_func B C S t T T0
    (@kernel_presentation_structure C S t T W P)
    (@cokernel_presentation_structure C S t T0 V Q) A D h;
