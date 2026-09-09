/* Declaration/usability consumer. Runtime retains formal observations;
   explicit equality witnesses compare with the original selected operations. */
require open emdash.emdash3_2_kernel_adjunction_presentations;

// Proof-time object agreement, not a runtime change of owner.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @eq_refl (Obj C) (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
  : τ (@= (Obj C) (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d) (@kernel_presentation_selected_object C S W d));

assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @fapp0 _ _ (@kernel_presentation_func C S t T W P) d ≡ @kernel_presentation_selected_object C S W d;

// Nonidentity arrow comparison uses the actual chosen lift/colift.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (d0 d1 : τ (Functor WalkingArrow_cat C)) (eta : τ (@Transf WalkingArrow_cat C d0 d1)) ⊢
  @eq_refl (Hom C (@kernel_presentation_selected_object C S W d0) (@kernel_presentation_selected_object C S W d1))
    (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 eta)
  : τ (@= (Hom C (@kernel_presentation_selected_object C S W d0) (@kernel_presentation_selected_object C S W d1))
      (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 eta)
      (@kernel_presentation_map_semantic C S W d0 d1 eta));

// Runtime identity/composition remain the generic functor laws.
assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d d (@id (Functor_cat WalkingArrow_cat C) d)
  ≡ @id C (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d);

assert [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W)) (d0 d1 d2 : τ (Functor WalkingArrow_cat C))
  (eta : τ (@Transf WalkingArrow_cat C d0 d1)) (theta : τ (@Transf WalkingArrow_cat C d1 d2)) ⊢
  @comp_fapp0 C _ _ _
    (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d1 d2 theta) (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 eta)
  ≡ @fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d2
      (@comp_fapp0 (Functor_cat WalkingArrow_cat C) d0 d1 d2 theta eta);

// An unrelated arrow of the same type is not accepted as the selected map.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W)) (d0 d1 : τ (Functor WalkingArrow_cat C))
  (eta : τ (@Transf WalkingArrow_cat C d0 d1))
  (other : τ (Hom C (@kernel_presentation_selected_object C S W d0) (@kernel_presentation_selected_object C S W d1))) ⊢
  @eq_refl (Hom C (@kernel_presentation_selected_object C S W d0) (@kernel_presentation_selected_object C S W d1))
    (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 eta)
  : τ (@= (Hom C (@kernel_presentation_selected_object C S W d0) (@kernel_presentation_selected_object C S W d1))
      (@fapp1_fapp0 _ _ (@kernel_presentation_func C S t T W P) d0 d1 eta) other);

// Further directed Hom action remains available on the whole functor.
type λ C : Cat, λ S : τ (@PreadditiveCategory C), λ t : τ (Obj C),
  λ T : τ (@TerminalObject C t), λ W : τ (@HasComputationalKernels C S),
  λ P : τ (@KernelPresentation C S t T W),
  λ d0 : τ (Functor WalkingArrow_cat C), λ d1 : τ (Functor WalkingArrow_cat C),
  λ eta : τ (@Transf WalkingArrow_cat C d0 d1), λ theta : τ (@Transf WalkingArrow_cat C d0 d1),
  @fapp1_func _ _ (@fapp1_func _ _ (@kernel_presentation_func C S t T W P) d0 d1) eta theta;

/* Actual zero-embedding specialization of the generic Došen rectangle. */


assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (S : τ (@PreadditiveCategory C)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (X X' : τ (Obj C))
  (Y : τ (Obj (Functor_cat WalkingArrow_cat C)))
  (g : τ (Hom C X X'))
  (f : τ (Hom (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X') Y)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P))
      (@id_func (Functor_cat WalkingArrow_cat C))
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X')
      Y
      (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P))
      f)
    (@fapp1_fapp0
      C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
      X
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X'))
      (@tapp1_fapp0
        C C
        (@id_func C)
        (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@terminal_arrow_diagram_func C t T))
        X X'
        (@unit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P))
        g))
  ≡ comp_fapp0 f (@fapp1_fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X X' g);

/* Actual zero-embedding specialization of the generic Došen rectangle. */


assert (C : Cat) (t : τ (Obj C)) (T : τ (@TerminalObject C t))
  (S : τ (@PreadditiveCategory C)) (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W))
  (X : τ (Obj C))
  (Y' Y : τ (Obj (Functor_cat WalkingArrow_cat C)))
  (f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) Y')))
  (g : τ (Hom (Functor_cat WalkingArrow_cat C) Y' Y)) ⊢
  comp_fapp0
    (@fapp1_fapp0
      (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P)
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) Y'))
      Y
      (@tapp1_fapp0
        (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
        (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P))
        (@id_func (Functor_cat WalkingArrow_cat C))
        Y' Y
        (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P))
        g))
    (@tapp1_fapp0
      C C
      (@id_func C)
      (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) (@terminal_arrow_diagram_func C t T))
      X
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) Y')
      (@unit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P))
      f)
  ≡ comp_fapp0 (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) Y' Y g) f;
