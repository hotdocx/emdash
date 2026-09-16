require open emdash.emdash3_2_one_cat_categorical_exactness;
/* The original canonical Im→Ker routes commute through the native point comparison. */
require open emdash.emdash3_2_image_family_point_comparisons;
require open emdash.emdash3_2_one_cat_image_kernel_point_paths;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K))
 ⊢ (@one_cat_image_kernel_point_path K C S C1 t T T0 P Q A D h N x) : τ (@= (Hom C (@fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t
  T T0 P Q) (@zero_arrow_family_incoming_func K C t T A D h)) x) (@fapp0 K C (@kernel_adjunction_family_func K C
  S t T P D) x))
    (@comp_fapp0 C (@fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S
  t T T0 P Q) (@zero_arrow_family_incoming_func K C t T A D h)) x) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T
  T0 P Q) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
  (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@zero_arrow_cone_image_kernel_transf C S C1 t T T0 P Q N)) (@image_family_global_point_map K C S C1 t T T0 P
  Q A D h x))
    (@tapp0_fapp0 K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func K C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x
  (@one_cat_image_to_kernel_transf K C S C1 t T T0 P Q A D h N)));
