require open emdash.emdash3_2_zero_arrow_cone_homology;

// Generic H identity/composition and further Hom action on the native source.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) (z : τ (Obj (@ZeroArrowCone_cat C t T))) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) z z (@id (@ZeroArrowCone_cat C t T) z) ≡ @id C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) z);
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) (x y z : τ (Obj (@ZeroArrowCone_cat C t T))) (f : τ (Hom (@ZeroArrowCone_cat C t T) x y)) (g : τ (Hom (@ZeroArrowCone_cat C t T) y z)) ⊢
  @comp_fapp0 C _ _ _ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) y z g) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x y f)
  ≡ @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x z (@comp_fapp0 (@ZeroArrowCone_cat C t T) x y z g f);

// Constructor-visible point agrees with the original selected kernel lift/cokernel.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) (A0 : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h0 : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A0) d)) ⊢
  @zero_arrow_cone_homology_object_path C S C1 t T T0 W V P Q (@zero_arrow_cone_obj C t T A0 d h0)
  : τ (@= (Obj C) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@zero_arrow_cone_obj C t T A0 d h0))
      (@computational_cokernel_object C S A0 (@kernel_presentation_selected_object C S W d)
        (@kernel_presentation_lift_semantic C S t T W A0 d h0)
        (V A0 (@kernel_presentation_selected_object C S W d)
          (@kernel_presentation_lift_semantic C S t T W A0 d h0))));

type λ C : Cat, λ S : τ (@PreadditiveCategory C), λ C1 : τ (IsNCat (cat_succ cat_zero) C),
  λ t : τ (Obj C), λ T : τ (@TerminalObject C t), λ T0 : τ (@TerminalObject (Op_cat C) t),
  λ W : τ (@HasComputationalKernels C S), λ V : τ (@HasComputationalCokernels C S),
  λ P : τ (@KernelPresentation C S t T W), λ Q : τ (@CokernelPresentation C S t T0 V),
  λ x : τ (Obj (@ZeroArrowCone_cat C t T)), λ y : τ (Obj (@ZeroArrowCone_cat C t T)), λ f : τ (Hom (@ZeroArrowCone_cat C t T) x y), λ g : τ (Hom (@ZeroArrowCone_cat C t T) x y),
  @fapp1_func _ _ (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x y) f g;

// Further Hom action also computes its generic identity.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) (x y : τ (Obj (@ZeroArrowCone_cat C t T))) (f : τ (Hom (@ZeroArrowCone_cat C t T) x y)) ⊢
  @fapp1_fapp0 (Hom_cat (@ZeroArrowCone_cat C t T) x y)
    (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) y))
    (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x y) f f (@id (Hom_cat (@ZeroArrowCone_cat C t T) x y) f)
  ≡ @id (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) y))
      (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x y f);

// A different arrow of the correct type is not accepted as H[f].
assertnot [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) (x y : τ (Obj (@ZeroArrowCone_cat C t T))) (f : τ (Hom (@ZeroArrowCone_cat C t T) x y))
  (other : τ (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) y))) ⊢
  eq_refl (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x y f)
  : τ (@= (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) y))
      (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) x y f) other);
