/* Whole H accepts original raw chain data before any kernel selection. */
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;
require open emdash.emdash3_2_kernel_cokernel_adjunction_mates;

// The universal whole observation at the raw input is the constructed map.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [X A B : τ (Obj C)] (b : τ (Hom C X A)) (d : τ (Hom C A B))
  (zero : τ (@= (Hom C X B) (@comp_fapp0 C X A B d b)
    (@preadditive_hom_zero C S X B)))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
  @tapp0_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    _ _ (@zero_composite_native_cone C S C1 t T X A B b d zero) (@zero_arrow_cone_universal_transf C C1 t T) ≡ (@terminal_zero_composite_transf C S C1 t T X A B b d zero);

// Proof-only generic observation through the whole adjunction comparison.
// It composes existing paths; it installs no conversion or runtime rule.
symbol review_boundary_mate_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (@= (Hom C (@fapp0 K C A x)
      (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x))
    (@tapp0_fapp0 K C A (@kernel_adjunction_family_func K C S t T P D) x
      (@kernel_adjunction_family_boundary_transf K C S t T P A D h))
    (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T P (@fapp0 K C A x)
      (@fapp0 K (Functor_cat WalkingArrow_cat C) D x))
      (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) _ D x h)))
≔ @eq_sym _ _ _
    (@eq_ap
      (Functor (Hom_cat (Functor_cat WalkingArrow_cat C)
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@fapp0 K C A x))
        (@fapp0 K (Functor_cat WalkingArrow_cat C) D x))
        (Hom_cat C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x)))
      (Hom C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x))
      (λ F : τ (Functor (Hom_cat (Functor_cat WalkingArrow_cat C)
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@fapp0 K C A x))
        (@fapp0 K (Functor_cat WalkingArrow_cat C) D x))
        (Hom_cat C (@fapp0 K C A x) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D) x))),
        @fapp0 _ _ F (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) _ D x h))
      _ _ (@adjunction_transpose_semantic_path C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P) (@fapp0 K C A x)
        (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)));

// Specialize the generic theorem at the actual raw native input.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [X A B : τ (Obj C)] (b : τ (Hom C X A)) (d : τ (Hom C A B))
  (zero : τ (@= (Hom C X B) (@comp_fapp0 C X A B d b)
    (@preadditive_hom_zero C S X B)))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
  @review_boundary_mate_path (@ZeroArrowCone_cat C t T) C S t T P
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) (@zero_composite_native_cone C S C1 t T X A B b d zero)
  : τ (@= (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@walking_arrow_func C A B d))) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C _ _ (@zero_composite_native_cone C S C1 t T X A B b d zero) (@kernel_adjunction_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))) (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T P X (@walking_arrow_func C A B d)) (@terminal_zero_composite_transf C S C1 t T X A B b d zero)));

// Global H is formed using only the supplied whole adjunction structures.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [X A B : τ (Obj C)] (b : τ (Hom C X A)) (d : τ (Hom C A B))
  (zero : τ (@= (Hom C X B) (@comp_fapp0 C X A B d b)
    (@preadditive_hom_zero C S X B)))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
  @fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@zero_composite_native_cone C S C1 t T X A B b d zero)
  : τ (Obj C);
