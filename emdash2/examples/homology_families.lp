/* Whole H and nonidentity base-arrow observations. */
require open emdash.emdash3_2_homology_family_selected_views;

// Generic computation, with its existing accumulation orientation.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B)) ⊢
  @fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b b (@id B b) ≡ @id C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b);
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (a b c : τ (Obj B)) (p : τ (Hom B a b)) (q : τ (Hom B b c)) ⊢
  @comp_fapp0 C _ _ _
    (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b c q) (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) a b p)
  ≡ @fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) a c (@comp_fapp0 B a b c q p);

// Boundary-arrow family retains the actual whole transformation.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) ⊢
  @diagram_family_transf B WalkingArrow_cat C (@kernel_family_boundary_diagram_func B C S t T W P A D h)
    walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ (@kernel_family_boundary_transf B C S t T W P A D h);
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) c) walking_arrow_src
    (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b c p)
  ≡ @fapp1_fapp0 B C A b c p;
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) c) walking_arrow_tgt
    (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b c p)
  ≡ @fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) b c p;

// A unrelated arrow between the same H objects is not the selected H[p].
assertnot [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c))
  (other : τ (Hom C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) c))) ⊢
  eq_refl (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b c p)
  : τ (@= (Hom C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) c))
      (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b c p) other);

// The complete higher Hom functor remains formed; no dimension cap.
type λ B : Cat, λ C : Cat, λ S : τ (@PreadditiveCategory C), λ t : τ (Obj C),
  λ T : τ (@TerminalObject C t), λ T0 : τ (@TerminalObject (Op_cat C) t),
  λ W : τ (@HasComputationalKernels C S), λ V : τ (@HasComputationalCokernels C S),
  λ P : τ (@KernelPresentation C S t T W), λ Q : τ (@CokernelPresentation C S t T0 V),
  λ A : τ (Functor B C), λ D : τ (Functor B (Functor_cat WalkingArrow_cat C)),
  λ h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D),
  λ b : τ (Obj B), λ c : τ (Obj B), λ p : τ (Hom B b c), λ q : τ (Hom B b c),
  @fapp1_func _ _ (@fapp1_func B C (@homology_family_func B C S t T T0 W V P Q A D h) b c) p q;

// Named comparisons are usable without re-elaborating a large raw eq_refl.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B)) ⊢
  @homology_family_object_path B C S t T T0 W V P Q A D h b
  : τ (@= (Obj C) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b)
      (@homology_family_selected_object B C S t T W V A D h b));
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @homology_family_map_path B C S t T T0 W V P Q A D h b c p
  : τ (@= (Hom C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) c))
      (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b c p)
      (@cokernel_presentation_map_semantic C S V (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b) (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) c) (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_family_boundary_diagram_func B C S t T W P A D h) b c p)));

// An additional directed-Hom level still computes its generic identity.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @fapp1_fapp0 (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) c))
    (@fapp1_func B C (@homology_family_func B C S t T T0 W V P Q A D h) b c) p p (@id (Hom_cat B b c) p)
  ≡ @id (Hom_cat C (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b) (@fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) c)) (@fapp1_fapp0 B C (@homology_family_func B C S t T T0 W V P Q A D h) b c p);
