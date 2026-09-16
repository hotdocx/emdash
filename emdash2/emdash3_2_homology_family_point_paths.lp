/* Original H quotient compatibility through whole categorical comparisons. */
require open emdash.emdash3_2_homology_family_point_comparisons;
require open emdash.emdash3_2_strict_transfor_component_paths;
require open emdash.emdash3_2_one_cat_cokernel_family_projection_paths;
require open emdash.emdash3_2_one_cat_homology_cover_maps;

symbol homology_family_global_point_projection_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))))
  (@comp_fapp0 C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x)) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
  (@homology_family_global_point_map K C S C1 t T T0 P Q A D h x) (@tapp0_fapp0 (Functor_cat
  WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@cokernel_adjunction_projection
  C S t T0 Q))) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat
  C t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@cokernel_adjunction_projection C S t T0 Q)))
≔ @strict_component_naturality_path (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T0 Q)
  (@cokernel_adjunction_projection C S t T0 Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@fapp0 (@ZeroArrowCone_cat C t
  T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@homology_family_global_boundary_point_map K C S C1 t T P A D h x);


symbol cokernel_family_projection_at_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (D : τ (Functor K (Functor_cat WalkingArrow_cat C))) (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) D) x) (@fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) x)) (@tapp0_fapp0 K C
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) D) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  S t T0 Q) D) x (@cokernel_adjunction_family_projection_transf K C S t T0 Q D)) (@tapp0_fapp0
  (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  (@cokernel_adjunction_projection C S t T0 Q)))
≔ @eq_ap (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) D) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) (Hom C (@fapp0 K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) D) x) (@fapp0 K
  C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) x))
 (λ e : τ (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) D) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)), @tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) D)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) x e) _ _
 (@one_cat_cokernel_family_projection_whisker_path K C S C1 t T0 Q D);

// Compare the actual whole H quotients, not only a separate scalar view.
symbol homology_family_global_point_quotient_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 : τ (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))))
  (@comp_fapp0 C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x)) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
  (@homology_family_global_point_map K C S C1 t T T0 P Q A D h x) (@tapp0_fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)) x
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)))) (@tapp0_fapp0 (@ZeroArrowCone_cat
  C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@zero_arrow_family_point_input K C t T A D h x)
  (@cokernel_adjunction_family_projection_transf (@ZeroArrowCone_cat C t T) C S t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)))))
≔ @eq_trans _ _ _ _
 (@eq_ap (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x))) (Hom C
  (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))))
  (λ e : τ (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x))),
  (@comp_fapp0 C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) walking_arrow_tgt) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x)) (@fapp0
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func
  C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
  (@homology_family_global_point_map K C S C1 t T T0 P Q A D h x) e)) _ _
  (@cokernel_family_projection_at_path K C S C1 t T0 Q (@kernel_adjunction_family_boundary_diagram_func K
  C S t T P A D h) x))
 (@eq_trans _ _ _ _ (@homology_family_global_point_projection_path K C S C1 t T T0 P Q A D h x)
  (@eq_sym _ _ _ (@cokernel_family_projection_at_path (@ZeroArrowCone_cat C t T) C S C1 t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))));

// Retain the actual target input and its whole diagram action; no presentation is identified.
symbol homology_family_native_comparison_quotient_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 (Y : τ (Obj (@ZeroArrowCone_cat C t T))) (n : τ (Hom (@ZeroArrowCone_cat C t T)
  (@zero_arrow_family_point_input K C t T A D h x) Y))
 : τ (@= (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C
  t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y))
  (@comp_fapp0 C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h
  x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x))
  (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y)
  (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0
  K (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)
  x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y)
  (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input K C t T A D h x) Y n) (@homology_family_global_point_map K C S C1 t T T0
  P Q A D h x)) (@tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)) x
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)))) (@comp_fapp0 C (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_diagram_func C t T)) Y) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y) (@tapp0_fapp0 (@ZeroArrowCone_cat C t
  T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func
  C t T)) (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y
  (@homology_adjunction_family_projection_transf (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) (@zero_arrow_family_point_input K C t T A D h x) Y n)))
≔ @eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc C (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t
  T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x)) (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C
  t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y)
  (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input K C t T A D h x) Y n) (@homology_family_global_point_map K C S C1 t T T0
  P Q A D h x) (@tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)) x
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h)))))
 (@eq_trans _ _ _ _
  (@eq_ap (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h
  x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))) (Hom C
  (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T
  P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y))
   (λ e : τ (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T))
  (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat
  C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))),
  (@comp_fapp0 C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func (@ZeroArrowCone_cat
  C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h
  x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) Y)
  (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input K C t T A D h x) Y n) e)) _ _
   (@homology_family_global_point_quotient_path K C S C1 t T T0 P Q A D h x))
  (@strict_component_naturality_path (@ZeroArrowCone_cat C t T) C (@kernel_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T))
  (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@homology_adjunction_family_projection_transf (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x) Y n));
