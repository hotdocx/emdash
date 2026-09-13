/* Native source formation and global H without selected universals. */
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;


// The native object is formed before any K/Q operation is applied.
assert [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A0 : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d)) ⊢ (@zero_arrow_cone_obj C t T A0 d h0) : τ (Obj (@ZeroArrowCone_cat C t T));

// Canonical whole input observation retains the supplied diagram map h0.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A0 : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d)) ⊢
  @tapp0_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) _ _ (@zero_arrow_cone_obj C t T A0 d h0) (@zero_arrow_cone_universal_transf C C1 t T) ≡ h0;

// Its actual boundary is the whole-kernel mate formula, without a chosen lift.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A0 : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d)) ⊢
  @tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_cone_obj C t T A0 d h0) (@kernel_adjunction_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  ≡ @comp_fapp0 C _ _ _
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d h0)
      (@tapp0_fapp0 C C (@id_func C)
        (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@terminal_arrow_diagram_func C t T)) A0
        (@unit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
          (@kernel_adjunction_evidence C S t T P)));

// Global H's ordinary diagram action is its actual family action.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (z w : τ (Obj (@ZeroArrowCone_cat C t T))) (f : τ (Hom (@ZeroArrowCone_cat C t T) z w)) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) z w f
  ≡ @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
      (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)) z w f;

// H retains Q at the actual native boundary diagram, with no reselection.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) (A0 : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d)) ⊢
  @fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_arrow_cone_obj C t T A0 d h0)
  ≡ @fapp0 (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T0 Q)
      (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
      (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
      (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_cone_obj C t T A0 d h0));
