/* The original whole coimage functor acts on the native point-diagram equivalence.
   Preserve the actual objects and the same selected inverse data. */
require open emdash.emdash3_2_zero_arrow_family_point_diagrams;
require open emdash.emdash3_2_image_coimage_adjunction_families;

// Coim acts on the native comparison of the original incoming diagrams.
symbol coimage_family_global_point_map [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))))
≔ @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 K (Functor_cat
  WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x);

// The same Coim action maps its original fixed-forward equivalence.
symbol coimage_family_global_point_equiv [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
  : τ (@OmegaEquivAlong C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@coimage_family_global_point_map K C S C1 t T T0 P
  Q A D h x))
≔ @omega_equiv_along_fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x)
    (@zero_arrow_family_point_diagram_equiv K C C1 t T A D h x);
