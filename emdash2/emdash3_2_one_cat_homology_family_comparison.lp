/* The whole native H-family comparison, with literal original endpoints.
   The actual boundary-diagram comparison retains both maps and laws; the
   original whole Q then acts on it. Paths occur only as ordinary laws or
   proof-valued modification cells, never to cast an operational functor.
   This is an ordinary-target construction under the original K/Q structures. */

require open emdash.emdash3_2_one_cat_zero_arrow_family_classification;

require open emdash.emdash3_2_homology_adjunction_families;


// Apply the original whole kernel mate to the retained triangle isomorphism.
symbol one_cat_kernel_family_triangle_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
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
  h) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)))
≔ @iso_evidence_fmap (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) (Hom_cat (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T
  P D)) (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)
  (@one_cat_zero_arrow_family_triangle_evidence B C C1 t T A D h);

protected symbol homology_family_comparison_native_boundary [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P
  (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)))
≔ @transf_prewhisker B (@ZeroArrowCone_cat C t T) C (@one_cat_zero_arrow_family_func B C C1 t T A D h)
  (@zero_arrow_cone_first_func C t T) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T))
  (@kernel_adjunction_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T P
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T));

protected symbol homology_family_comparison_family_boundary [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B C A (@kernel_adjunction_family_func B C S t T P D))
≔ @kernel_adjunction_family_boundary_transf B C S t T P A D h;

protected symbol homology_family_comparison_kernel_target_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P D))
≔ @transf_postwhisker B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@one_cat_zero_arrow_family_target_func B C C1
  t T A D h) D (@one_cat_zero_arrow_family_target_to B C C1 t T A D h);

protected symbol homology_family_comparison_boundary_left [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
≔ @comp_fapp0 (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T
  P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P) (@homology_family_comparison_native_boundary B C C1 t T A D h S P);

protected symbol homology_family_comparison_boundary_right [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
≔ @comp_fapp0 (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@kernel_adjunction_family_func B C S t
  T P D)
  (@homology_family_comparison_family_boundary B C C1 t T A D h S P) (@one_cat_zero_arrow_family_source_to B C C1 t T A D h);

protected symbol homology_family_comparison_boundary_left_point_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T)) (x : τ (Obj B))
 : τ (@= (Hom C (@fapp0 B C A x) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x))
     (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D) x
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P))
     (@tapp0_fapp0 B C A (@kernel_adjunction_family_func B C S t T P D) x (@homology_family_comparison_family_boundary B C C1 t
  T A D h S P)))
≔ @one_cat_transf_identity_path (@ZeroArrowCone_cat C t T) C C1 (@zero_arrow_cone_first_func C t T)
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) (@kernel_adjunction_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))
   (@fapp0 B (@ZeroArrowCone_cat C t T) (@one_cat_zero_arrow_family_func B C C1 t T A D h) x);

protected symbol homology_family_comparison_boundary_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (Hom (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P))
≔ @one_cat_modification B C C1 (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S
  t T P D) (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
   (λ x : τ (Obj B), @path_to_hom (Hom_cat C (@fapp0 B C A x) (@fapp0 B C (@kernel_adjunction_family_func
  B C S t T P D) x)) (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C
  S t T P D) x (@homology_family_comparison_boundary_left B C C1 t T A D h S P)) (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) (@kernel_adjunction_family_func B C S t T P D) x (@homology_family_comparison_boundary_right B C C1 t T A D h S P))
  (@homology_family_comparison_boundary_left_point_path B C C1 t T A D h S P x));

protected symbol homology_family_comparison_boundary_from [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (Hom (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_left B C C1 t T A D h S P))
≔ @one_cat_modification B C C1 (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S
  t T P D) (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
   (λ x : τ (Obj B), @path_to_hom (Hom_cat C (@fapp0 B C A x) (@fapp0 B C (@kernel_adjunction_family_func
  B C S t T P D) x)) (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C
  S t T P D) x (@homology_family_comparison_boundary_right B C C1 t T A D h S P)) (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) (@kernel_adjunction_family_func B C S t T P D) x (@homology_family_comparison_boundary_left B C C1 t T A D h S P)) (@eq_sym
  (Obj (Hom_cat C (@fapp0 B C A x) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x)))
  (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D) x
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P)) (@tapp0_fapp0 B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D) x (@homology_family_comparison_boundary_right B C C1 t T A D h S P))
  (@homology_family_comparison_boundary_left_point_path B C C1 t T A D h S P x)));

protected symbol homology_family_comparison_boundary_left_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (Hom (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P
  D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)) (@comp_fapp0
  (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_from B C C1 t T A D h S P) (@homology_family_comparison_boundary_to
  B C C1 t T A D h S P)) (@id (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)))
≔ @is_contr_center (@= (Hom (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P)) (@comp_fapp0 (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_from B C C1 t T A D h S P) (@homology_family_comparison_boundary_to B C C1 t T A D h S P)) (@id (@Transf_cat B
  C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B
  C C1 t T A D h S P))) ((@discrete_hom_is_prop (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) ((@one_cat_functor_category B C C1) (@one_cat_zero_arrow_family_source_func B C C1
  t T A D h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P)) (@comp_fapp0 (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_from B C C1 t T A D h S P) (@homology_family_comparison_boundary_to B C C1 t T A D h S P)) (@id (@Transf_cat B
  C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_left B
  C C1 t T A D h S P)));

protected symbol homology_family_comparison_boundary_right_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (Hom (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P
  D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P))
  (@comp_fapp0 (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T
  P D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_left B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_right B C C1 t T A D h S P) (@homology_family_comparison_boundary_to B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_from B C C1 t T A D h S P)) (@id (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)))
≔ @is_contr_center (@= (Hom (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_right B C C1 t T A D h S P)) (@comp_fapp0 (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_from B C C1 t T A D h S P)) (@id (@Transf_cat B
  C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right
  B C C1 t T A D h S P))) ((@discrete_hom_is_prop (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) ((@one_cat_functor_category B C C1) (@one_cat_zero_arrow_family_source_func B C C1
  t T A D h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_right B C C1 t T A D h S P)) (@comp_fapp0 (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D
  h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_from B C C1 t T A D h S P)) (@id (@Transf_cat B
  C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D)) (@homology_family_comparison_boundary_right
  B C C1 t T A D h S P)));

protected symbol homology_family_comparison_boundary_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P))
≔ @iso_evidence_intro (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C
  S t T P D)) (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_from B C C1 t T A D h S P)
   (@homology_family_comparison_boundary_left_law B C C1 t T A D h S P) (@homology_family_comparison_boundary_right_law B C C1 t T A D h S P);

require open emdash.emdash3_2_one_cat_arrow_diagrams;

protected symbol homology_family_comparison_boundary_diagram_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T
  A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@kernel_adjunction_family_boundary_diagram_func B C S t T
  P A D h))
≔ @sym_func_func_transf WalkingArrow_cat B C
   (@walking_arrow_func (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func
  B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
   (@walking_arrow_func (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_family_boundary B C C1 t T A D h S P))
   (@one_cat_square_diagram_transf (Functor_cat B C) (@one_cat_functor_category B C C1)
     (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t
  T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)
  (@homology_family_comparison_family_boundary B C C1 t T A D h S P)
     (@one_cat_zero_arrow_family_source_to B C C1 t T A D h) (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_to B
  C C1 t T A D h S P));

require open emdash.emdash3_2_omega_equiv_inverse_square;

protected symbol homology_family_comparison_source_equiv [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1 t T A D
  h))
≔ @iso_evidence_omega_along (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A
  (@represented_comma_family_source_evidence B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A
  D h);

protected symbol homology_family_comparison_kernel_target_equiv [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1
  t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to B C C1 t T A D h S
  P))
≔ @iso_evidence_omega_along (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B
  C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@iso_evidence_fmap (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@one_cat_zero_arrow_family_target_func B C C1 t T A D h) D (@omega_equiv_along_iso_evidence (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@one_cat_zero_arrow_family_target_func B C C1 t T A D h) D (@one_cat_represented_comma_family_target_to B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A D h (@one_cat_functor_category
  WalkingArrow_cat C C1)) (@one_cat_represented_comma_family_target_equiv B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A D h (@one_cat_functor_category WalkingArrow_cat C C1))));

protected symbol homology_family_comparison_boundary_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P))
≔ @groupoidal_arrow_to_path (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P D)) (@discrete_cat_is_groupoidal (@Transf_cat B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D))
  ((@one_cat_functor_category B C C1) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C
  S t T P D)))
  (@homology_family_comparison_boundary_left B C C1 t T A D h S P) (@homology_family_comparison_boundary_right B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_to B C C1 t T A D h S P);

protected symbol homology_family_comparison_inverse_boundary_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C A (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)))
  (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@omega_equiv_along_left_inv (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func
  B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to B C C1 t T A D
  h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P)) (@homology_family_comparison_family_boundary B C C1 t T A D h S P))
  (@comp_fapp0 (Functor_cat B C) A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1
  t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P))))
≔ @omega_equiv_inverse_square_path (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P) (@homology_family_comparison_family_boundary B C C1 t T A D h S P)
  (@one_cat_zero_arrow_family_source_to B C C1 t T A D h) (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P) (@homology_family_comparison_source_equiv B C
  C1 t T A D h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P) (@homology_family_comparison_boundary_path B C C1 t T A D h
  S P);

protected symbol homology_family_comparison_boundary_diagram_from [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t
  T P A D h) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)))
≔ @sym_func_func_transf WalkingArrow_cat B C
  (@walking_arrow_func (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_family_boundary B C C1 t T A D h S P)) (@walking_arrow_func (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C
  C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@one_cat_square_diagram_transf (Functor_cat B C) (@one_cat_functor_category B C C1)
    A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_family_boundary B C
  C1 t T A D h S P) (@homology_family_comparison_native_boundary B C C1 t T A D h S P) (@omega_equiv_along_left_inv (Functor_cat
  B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1 t T A D h) (@homology_family_comparison_source_equiv B C C1 t T
  A D h S P)) (@omega_equiv_along_left_inv (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P
  (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to
  B C C1 t T A D h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P))
    (@path_to_hom (Hom_cat (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B
  C C1 t T A D h))) (@comp_fapp0 (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@omega_equiv_along_left_inv (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func
  B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to B C C1 t T A D
  h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P)) (@homology_family_comparison_family_boundary B C C1 t T A D h S P))
  (@comp_fapp0 (Functor_cat B C) A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1
  t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P))) (@homology_family_comparison_inverse_boundary_path B C C1 t T A D h S
  P)));

require open emdash.emdash3_2_one_cat_diagram_family_reflection;

protected symbol homology_family_comparison_diagram_left_source_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T
  A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A
  D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary
  B C C1 t T A D h S P)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P)) walking_arrow_src) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))) walking_arrow_src))
≔ @eq_trans (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T
  A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A
  D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary
  B C C1 t T A D h S P)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P)) walking_arrow_src) (@comp_fapp0 (Functor_cat B C)
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@omega_equiv_along_left_inv
  (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1 t T A D h)
  (@homology_family_comparison_source_equiv B C C1 t T A D h S P)) (@one_cat_zero_arrow_family_source_to B C C1 t T A D h)) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))) walking_arrow_src)
  (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S
  t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P))
  (@eq_trans (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) (@comp_fapp0
  (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1
  t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P)) (@one_cat_zero_arrow_family_source_to B C C1 t T A D h)) (@id
  (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P))) walking_arrow_src)
    (@omega_equiv_along_left_law (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C
  C1 t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P)) (@eq_sym (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T
  A D h) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P))) walking_arrow_src) (@id (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_src) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)))));

protected symbol homology_family_comparison_diagram_left_target_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P)) walking_arrow_tgt) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))) walking_arrow_tgt))
≔ @eq_trans (@Transf B C (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P)) walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func
  B C C1 t T A D h)) (@omega_equiv_along_left_inv (Functor_cat B C) (@kernel_adjunction_family_func B C S
  t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P))
  (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P))) walking_arrow_tgt)
  (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt
    (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S
  t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P))
  (@eq_trans (@Transf B C (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@comp_fapp0 (Functor_cat
  B C) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func
  B C C1 t T A D h)) (@omega_equiv_along_left_inv (Functor_cat B C) (@kernel_adjunction_family_func B C S
  t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P))
  (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P)) (@id (Functor_cat B C) (@kernel_adjunction_family_func B
  C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P))) walking_arrow_tgt)
    (@omega_equiv_along_left_law (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P
  (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to
  B C C1 t T A D h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P)) (@eq_sym (@Transf B C
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@sym_transf_tapp0_transf
  B WalkingArrow_cat C (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))) walking_arrow_tgt) (@id (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@fapp1_id_path
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B
  WalkingArrow_cat C walking_arrow_tgt) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)))));

protected symbol homology_family_comparison_diagram_left_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1
  t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A
  D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary
  B C C1 t T A D h S P))) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))))
≔ @one_cat_diagram_family_map_path B C C1 (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)))
  (@homology_family_comparison_diagram_left_source_law B C C1 t T A D h S P) (@homology_family_comparison_diagram_left_target_law B C C1 t T A D h S
  P);

protected symbol homology_family_comparison_diagram_right_source_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C A A) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@comp_fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t
  T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)) walking_arrow_src)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t
  T P A D h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_src))
≔ @eq_trans (@Transf B C A A) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@comp_fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t
  T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)) walking_arrow_src) (@comp_fapp0
  (Functor_cat B C) A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1 t T A D h)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1
  t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P))) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_src)
  (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@kernel_adjunction_family_boundary_diagram_func B C S
  t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A
  D h S P))
  (@eq_trans (@Transf B C A A) (@comp_fapp0 (Functor_cat B C) A (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A
  (@one_cat_zero_arrow_family_source_to B C C1 t T A D h) (@omega_equiv_along_left_inv (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t
  T A D h) A (@one_cat_zero_arrow_family_source_to B C C1 t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P))) (@id
  (Functor_cat B C) A) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_src)
    (@omega_equiv_left_as_right_law (Functor_cat B C) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B
  C C1 t T A D h) (@homology_family_comparison_source_equiv B C C1 t T A D h S P)) (@eq_sym (@Transf B C A A)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t
  T P A D h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_src) (@id (Functor_cat B C) A) (@fapp1_id_path (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@diagram_family_evaluation_func B WalkingArrow_cat C
  walking_arrow_src) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))));

protected symbol homology_family_comparison_diagram_right_target_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S
  t T P D)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@comp_fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t
  T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)) walking_arrow_tgt)
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t
  T P A D h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_tgt))
≔ @eq_trans (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B
  C S t T P D)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@comp_fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t
  T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)) walking_arrow_tgt) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D)
  (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P) (@omega_equiv_along_left_inv (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P)
  (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P))) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_tgt)
  (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt
    (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@kernel_adjunction_family_boundary_diagram_func B C S
  t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A
  D h S P))
  (@eq_trans (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B
  C S t T P D)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to B C C1 t T A D h S P)
  (@omega_equiv_along_left_inv (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func
  B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to B C C1 t T A D
  h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P))) (@id (Functor_cat B C)
  (@kernel_adjunction_family_func B C S t T P D)) (@sym_transf_tapp0_transf B WalkingArrow_cat C
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_tgt)
    (@omega_equiv_left_as_right_law (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P
  (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@kernel_adjunction_family_func B C S t T P D) (@homology_family_comparison_kernel_target_to
  B C C1 t T A D h S P) (@homology_family_comparison_kernel_target_equiv B C C1 t T A D h S P)) (@eq_sym (@Transf B C
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P D))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t
  T P A D h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@id (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  walking_arrow_tgt) (@id (Functor_cat B C) (@kernel_adjunction_family_func B C S t T P D))
  (@fapp1_id_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@diagram_family_evaluation_func B WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))));

protected symbol homology_family_comparison_diagram_right_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C
  S t T P A D h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)) (@comp_fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S
  t T P A D h) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C
  C1 t T A D h S P)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P))
  (@id (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B
  C S t T P A D h)))
≔ @one_cat_diagram_family_map_path B C C1 (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D
  h) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@comp_fapp0 (Functor_cat B
  (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t
  T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A D h S P)) (@id (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
  (@homology_family_comparison_diagram_right_source_law B C C1 t T A D h S P) (@homology_family_comparison_diagram_right_target_law B C C1 t T A D h S
  P);

protected symbol homology_family_comparison_boundary_diagram_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@kernel_adjunction_family_boundary_diagram_func B C S
  t T P A D h))
≔ @iso_evidence_intro (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@kernel_adjunction_family_boundary_diagram_func B C S
  t T P A D h) (@homology_family_comparison_boundary_diagram_to B C C1 t T A D h S P) (@homology_family_comparison_boundary_diagram_from B C C1 t T A
  D h S P)
  (@homology_family_comparison_diagram_left_law B C C1 t T A D h S P) (@homology_family_comparison_diagram_right_law B C C1 t T A D h S P);

require open emdash.emdash3_2_one_cat_diagram_family_reconstruction;

// Restrict the original native boundary diagram along Γ.
symbol one_cat_homology_family_native_diagram [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h));

require open emdash.emdash3_2_one_cat_arrow_family_isomorphisms;

protected symbol homology_family_comparison_native_generator_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (@= (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P
  (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@diagram_family_transf B WalkingArrow_cat C (@one_cat_homology_family_native_diagram B C
  C1 t T A D h S P) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@homology_family_comparison_native_boundary B
  C C1 t T A D h S P))
≔ @one_cat_diagram_family_transf_reindex_path B (@ZeroArrowCone_cat C t T) WalkingArrow_cat C C1
   (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator;

protected symbol homology_family_comparison_native_generator_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t
  T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)
  (@diagram_family_transf B WalkingArrow_cat C (@one_cat_homology_family_native_diagram B C C1 t T A D h S P)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @iso_evidence_sym (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S
  t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@diagram_family_transf B WalkingArrow_cat C
  (@one_cat_homology_family_native_diagram B C C1 t T A D h S P) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P)
  (@idtoiso_cat (@Transf_cat B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T
  P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))) (@diagram_family_transf B WalkingArrow_cat C (@one_cat_homology_family_native_diagram B
  C C1 t T A D h S P) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@homology_family_comparison_native_boundary
  B C C1 t T A D h S P) (@homology_family_comparison_native_generator_path B C C1 t T A D h S P));

protected symbol homology_family_comparison_native_introduced_diagram_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t
  T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@diagram_family_transf B WalkingArrow_cat C (@one_cat_homology_family_native_diagram B C C1 t T A D h S P)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
≔ @one_cat_arrow_family_comparison_evidence B C C1 (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)
  (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@homology_family_comparison_native_boundary B C C1 t T A D h S P) (@diagram_family_transf B WalkingArrow_cat C
  (@one_cat_homology_family_native_diagram B C C1 t T A D h S P) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@homology_family_comparison_native_generator_evidence B C C1 t T A D h S P);

protected symbol homology_family_comparison_native_diagram_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@one_cat_homology_family_native_diagram B C C1 t T A D h S P))
≔ @iso_evidence_comp (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t
  T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
  (@diagram_family_transf B WalkingArrow_cat C (@one_cat_homology_family_native_diagram B C C1 t T A D h S P)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_homology_family_native_diagram B C C1 t T A D h S
  P)
  (@one_cat_diagram_family_reconstruction_evidence B C C1 (@one_cat_homology_family_native_diagram B C C1 t T A D h S P))
  (@homology_family_comparison_native_introduced_diagram_evidence B C C1 t T A D h S P);

// Compare the original native and family diagrams with selected inverse data.
symbol one_cat_homology_family_diagram_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 : τ (IsoEvidence (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@one_cat_homology_family_native_diagram B C C1 t T A D h
  S P) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h))
≔ @iso_evidence_comp (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@one_cat_homology_family_native_diagram B C C1 t T A D
  h S P) (@transf_arrow_diagram_func B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B
  C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@homology_family_comparison_boundary_diagram_evidence B C C1 t T A D h S P)
  (@iso_evidence_sym (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@transf_arrow_diagram_func B C
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) (@kernel_adjunction_family_func B C S t T P (@one_cat_zero_arrow_family_target_func B C C1 t T A D
  h)) (@homology_family_comparison_native_boundary B C C1 t T A D h S P)) (@one_cat_homology_family_native_diagram B C C1 t T A D h S P)
  (@homology_family_comparison_native_diagram_reconstruction B C C1 t T A D h S P));

// Apply the original whole Q, retaining H_family≅H_native∘Γ at literal endpoints.
symbol one_cat_homology_family_comparison_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 : τ (IsoEvidence (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h)
  (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C
  (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h)))
≔ @iso_evidence_fmap (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
  (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) (@one_cat_homology_family_native_diagram B C C1 t T A D
  h S P)
   (@iso_evidence_sym (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@one_cat_homology_family_native_diagram B C C1 t T A
  D h S P) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
  (@one_cat_homology_family_diagram_evidence B C C1 t T A D h S P));
