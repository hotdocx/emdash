require open emdash.emdash3_2_one_cat_homology_family_comparison;
// catalog-area: Whole native homology family comparison

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T)) ⊢
 @iso_evidence_to (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@one_cat_adjunction_family_transpose_func B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C
  S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)) (@fapp0 (Hom_cat
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (Hom_cat (Functor_cat B C)
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)) (@one_cat_kernel_family_triangle_evidence B C C1 t T A D h S P)
 ≡ @fapp1_fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T
  P D)) (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@iso_evidence_to (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_evidence B C C1 t T A D h));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T)) ⊢
 @iso_evidence_from (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@one_cat_adjunction_family_transpose_func B C
  (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C
  S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)) (@fapp0 (Hom_cat
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (Hom_cat (Functor_cat B C)
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)) (@one_cat_kernel_family_triangle_evidence B C C1 t T A D h S P)
 ≡ @fapp1_fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T
  P D)) (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)
  (@iso_evidence_from (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_evidence B C C1 t T A D h));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
 @iso_evidence_to (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)
 ≡ @fapp1_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@one_cat_homology_family_native_diagram B C C1 t T A D
  h S P)
     (@iso_evidence_from (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@one_cat_homology_family_native_diagram B C C1 t T
  A D h S P) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@one_cat_homology_family_diagram_evidence B C C1 t T A D h S P));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
 @iso_evidence_from (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)
 ≡ @fapp1_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) (@one_cat_homology_family_native_diagram B C C1
  t T A D h S P) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
     (@iso_evidence_to (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@one_cat_homology_family_native_diagram B C C1 t T A
  D h S P) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@one_cat_homology_family_diagram_evidence B C C1 t T A D h S P));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
 @iso_evidence_left (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)
 : τ (@= (Hom (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@homology_adjunction_family_func B C S t T T0 P Q A D h))
     (@comp_fapp0 (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@homology_adjunction_family_func B C S t T T0 P Q A D h)
       (@iso_evidence_from (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)) (@iso_evidence_to (Functor_cat B C)
  (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T)
  C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)))
     (@id (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) ⊢
 @iso_evidence_right (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)
 : τ (@= (Hom (Functor_cat B C) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h)) (@comp_cat_fapp0 B
  (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h)))
     (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T)
  C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
       (@iso_evidence_to (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)) (@iso_evidence_from (Functor_cat B C)
  (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T)
  C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q)))
     (@id (Functor_cat B C) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))));
