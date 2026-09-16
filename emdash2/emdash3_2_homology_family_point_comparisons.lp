/* Compare actual boundary diagrams categorically, then apply the same Q.
   Earlier equality paths remain derived observations. The operational map
   uses whole diagram reconstruction with identity endpoint components.
   No H object is cast and no intermediate quotient is selected. */
require open emdash.emdash3_2_zero_arrow_family_point_inputs;
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;
require open emdash.emdash3_2_homology_adjunction_record_data;
require open emdash.emdash3_2_homology_family_point_diagrams;

// Canonical introduced diagram of the actual boundary at this point.
symbol kernel_boundary_point_diagram_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (@= (Functor WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@walking_arrow_func C (@fapp0 K C A x)
  (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x)) (@kernel_adjunction_semantic_boundary C S t T P (@fapp0 K C A x) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D x h))))
≔ @transf_arrow_diagram_point_path K C A (@kernel_adjunction_family_func K C S t T P D)
  (@kernel_adjunction_family_boundary_transf K C S t T P A D h) x;

// Compare the two existing boundary diagrams before applying Q.
symbol homology_family_global_boundary_point_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (@= (Functor WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C
  S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
≔ @eq_trans (Functor WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x) (@walking_arrow_func C (@fapp0 K C A x)
  (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x)) (@kernel_adjunction_semantic_boundary C S t T P (@fapp0 K C A x) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D x h))) (@fapp0 (@ZeroArrowCone_cat
  C t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C
  t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@kernel_boundary_point_diagram_path K C S t T P A D h x) (@eq_sym (Functor WalkingArrow_cat C) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func
  (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@walking_arrow_func C (@fapp0 K C A x) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
  S t T P) (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)) (@kernel_adjunction_semantic_boundary C S t T P
  (@fapp0 K C A x) (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D x h)))
  (@kernel_boundary_point_diagram_path (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)
  (@zero_arrow_family_point_input K C t T A D h x)));

// Original Q acts once on the comparison, retaining the two actual H objects.
symbol homology_family_global_point_map [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (Hom C (@fapp0 K C (@homology_adjunction_family_func K C S t T T0 P Q A D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input K C t T A D h x)))
≔ @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P A D h) x)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@homology_family_global_boundary_point_map K C S C1 t T P A D h x);

// The existing fixed-forward equivalence action maps the same selected inverse.
symbol homology_family_global_point_equiv [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (@OmegaEquivAlong C (@fapp0 K C (@homology_adjunction_family_func K C S t T T0 P Q A D h) x) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q)
  (@zero_arrow_family_point_input K C t T A D h x)) (@homology_family_global_point_map K C S C1 t T T0 P Q A D h
  x))
≔ @omega_equiv_along_fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func K C S t T P
  A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))
  (@homology_family_global_boundary_point_map K C S C1 t T P A D h x)
  (@homology_family_global_boundary_point_equiv K C S C1 t T P A D h x);
