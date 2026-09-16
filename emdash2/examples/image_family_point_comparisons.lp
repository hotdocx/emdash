/* Both actual inverse laws of Im applied to the retained input-diagram comparison. */
require open emdash.emdash3_2_image_family_point_comparisons;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 ⊢ (@omega_equiv_along_left_law C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0
  P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@image_family_global_point_map K C S C1 t T T0 P
  Q A D h x) (@image_family_global_point_equiv K C S C1 t T T0 P Q A D h x)) : τ (@= (Hom C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x))) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C)
  C (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@omega_equiv_along_left_inv C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@image_family_global_point_map K C S C1 t T T0 P
  Q A D h x) (@image_family_global_point_equiv K C S C1 t T T0 P Q A D h x)) (@image_family_global_point_map K C
  S C1 t T T0 P Q A D h x)) (@id C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0
  P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 ⊢ (@omega_equiv_along_right_law C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0
  P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@image_family_global_point_map K C S C1 t T T0 P
  Q A D h x) (@image_family_global_point_equiv K C S C1 t T T0 P Q A D h x)) : τ (@= (Hom C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))) (@comp_fapp0 C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@image_family_global_point_map K C S C1 t T T0 P
  Q A D h x) (@omega_equiv_along_right_inv C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C S t T T0 P Q) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@image_family_global_point_map K C S C1 t T T0 P
  Q A D h x) (@image_family_global_point_equiv K C S C1 t T T0 P Q A D h x))) (@id C (@fapp0 (Functor_cat
  WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))));
