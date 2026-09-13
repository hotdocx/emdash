/* Whole comparison at the one-way legacy adapters. No point reselection. */
require open emdash.emdash3_2_zero_arrow_cone_homology;

assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) ⊢
  @kernel_family_boundary_transf B C S t T W P A D h
  ≡ @kernel_adjunction_family_boundary_transf B C S t T (@kernel_presentation_structure C S t T W P) A D h;

assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) ⊢
  @homology_family_func B C S t T T0 W V P Q A D h
  ≡ @homology_adjunction_family_func B C S t T T0 (@kernel_presentation_structure C S t T W P) (@cokernel_presentation_structure C S t T0 V Q) A D h;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) ⊢
  @zero_arrow_cone_homology_func C S C1 t T T0 W V P Q
  ≡ @zero_arrow_cone_adjunction_homology_func C S C1 t T T0 (@kernel_presentation_structure C S t T W P) (@cokernel_presentation_structure C S t T0 V Q);
