/* Exactness at the original canonical comparison of a native zero-cone.
   Whole-family evaluation and categorical transport are derived operations. */
require open emdash.emdash3_2_one_cat_categorical_exactness;
require open emdash.emdash3_2_one_cat_natural_equivalence_transport;
require open emdash.emdash3_2_one_cat_image_kernel_point_paths;

// Exactness means ΩAlong on the original canonical Im→Ker at this native input.
symbol OneCatNativeExactAt [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (X : τ (Obj (@ZeroArrowCone_cat C t T))) : Grpd
≔ @OmegaEquivAlong C (@fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) X) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T)) X)
  (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) X (@zero_arrow_cone_image_kernel_transf C S C1 t T T0 P Q N));

// Transport along an equivalence of actual native inputs; no square is caller data.
symbol one_cat_native_exactness_transport [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 [X Y : τ (Obj (@ZeroArrowCone_cat C t T))] (m : τ (Hom (@ZeroArrowCone_cat C t T) X Y)) (M : τ
  (@OmegaEquivAlong (@ZeroArrowCone_cat C t T) X Y m))
 (E : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N X)) : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N Y)
≔ @one_cat_natural_equivalence_transport (@ZeroArrowCone_cat C t T) C C1 (@comp_cat_fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)))
  (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_diagram_func C t T))
  (@zero_arrow_cone_image_kernel_transf C S C1 t T T0 P Q N) X Y m M E;

// Evaluate the original whole witness and transport through the proved canonical comparison.
symbol one_cat_exact_family_at [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (x : τ (Obj K))
 (E : τ (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A D h N))
 : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N (@zero_arrow_family_point_input K C t T A D h x))
≔ (@omega_equiv_right_factor C (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@fapp0 (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T))
  (@zero_arrow_family_point_input K C t T A D h x))) (@fapp0 K C (@kernel_adjunction_family_func K C S t T P D)
  x) (@image_family_global_point_map K C S C1 t T T0 P Q A D h x) (@tapp0_fapp0 K C (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K
  C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) x (@one_cat_image_to_kernel_transf K C S C1 t T
  T0 P Q A D h N)) (@tapp0_fapp0 (@ZeroArrowCone_cat C t T) C (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func
  (@ZeroArrowCone_cat C t T) C t T (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T))) (@kernel_adjunction_family_func (@ZeroArrowCone_cat C t T) C S
  t T P (@zero_arrow_cone_diagram_func C t T)) (@zero_arrow_family_point_input K C t T A D h x)
  (@one_cat_image_to_kernel_transf (@ZeroArrowCone_cat C t T) C S C1 t T T0 P Q (@zero_arrow_cone_first_func C t
  T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) N))
  (@image_family_global_point_equiv K C S C1 t T T0 P Q A D h x) (@omega_equiv_along_fapp1_fapp0 (Functor_cat K
  C) C (@fapp0_func K C x) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K
  C t T A D h)) (@kernel_adjunction_family_func K C S t T P D) (@one_cat_image_to_kernel_transf K C S C1 t T
  T0 P Q A D h N) E) (@one_cat_image_kernel_point_path K C S C1 t T T0 P Q A D h N x));
