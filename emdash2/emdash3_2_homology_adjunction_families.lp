/* Whole homology from independent categorical universal structure.
   P and Q contain whole functors and native adjunction evidence. The coherent
   input is h:J∘A⇒D; no selected per-arrow kernel, cokernel or factor family
   is required. Computation stays at existing fapp/tapp and adjunction owners. */
require open emdash.emdash3_2_kernel_cokernel_adjunctions;

symbol kernel_adjunction_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (Functor B C)
≔ @comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D;

symbol kernel_adjunction_family_unit_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (A : τ (Functor B C))
  : τ (@Transf B C A
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)))
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B C C A (@id_func C)
      (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P) (@terminal_arrow_diagram_func C t T)))
    (@unit_adj_transf C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P));

symbol kernel_adjunction_family_action_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A))
      (@kernel_adjunction_family_func B C S t T P D))
≔ @fapp0 _ _ (@comp_cat_cov_fapp1_func B (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P)
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D) h;

// beta = (K h) ∘ (eta A), with associativity handled by existing usability.
symbol kernel_adjunction_family_boundary_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C A (@kernel_adjunction_family_func B C S t T P D))
≔ @comp_fapp0 (Functor_cat B C) A _ (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_action_transf B C S t T P A D h)
    (@kernel_adjunction_family_unit_transf B C S t T P A);

symbol kernel_adjunction_family_boundary_diagram_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (A : τ (Functor B C))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func B C A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h);

// H = Q applied to the whole boundary diagram family. No new primitive H.
symbol homology_adjunction_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (Functor B C)
≔ @comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h);
