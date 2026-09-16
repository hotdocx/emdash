/* Native comparison of the same point diagrams, with identity endpoint action.
   The existing reconstruction DefIso supplies the maps; no shape law is added. */
require open emdash.emdash3_2_zero_arrow_family_point_comparisons;
require open emdash.emdash3_2_one_cat_diagram_reconstruction;
require open emdash.emdash3_2_one_cat_diagram_map_paths;

// The two actual diagram generators agree by the original incoming observation paths.
symbol zero_arrow_family_point_generator_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
   : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))
≔ @eq_trans _ _ _ _ (@zero_arrow_incoming_at_point_path K C C1 t T A D h x) (@eq_sym _ _ _
  (@zero_arrow_incoming_at_point_path (@ZeroArrowCone_cat C t T) C C1 t T (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)
  (@zero_arrow_family_point_input K C t T A D h x)));

// Assemble the original diagrams through the existing reconstruction isomorphism.
symbol zero_arrow_family_point_diagram_map [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
    : τ (@Transf WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
≔ (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@one_cat_diagram_reconstruction_to C C1 (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@one_cat_square_diagram_transf C C1 (@fapp0 K C A x) (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@id C (@fapp0 K C A x)) (@id C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x)
  walking_arrow_src)) (@path_to_hom (Hom_cat C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@zero_arrow_family_point_generator_path K C C1 t T A D h x)))
  (@one_cat_diagram_reconstruction_from C C1 (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x))));

// The source component is the identity on the retained source object.
symbol zero_arrow_family_point_diagram_map_src_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
    : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat
  WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src (@zero_arrow_family_point_diagram_map K C
  C1 t T A D h x)) (@id C (@fapp0 K C A x)))
≔ @eq_refl (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (@id C (@fapp0 K C A x));

// The target component is the identity on the retained target object.
symbol zero_arrow_family_point_diagram_map_tgt_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
    : τ (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_tgt (@zero_arrow_family_point_diagram_map K C
  C1 t T A D h x)) (@id C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)))
≔ @eq_refl (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@id C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src));

// Reverse the same generator comparison and reconstruction maps.
symbol zero_arrow_family_point_diagram_inverse [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
    : τ (@Transf WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x))
≔ (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@one_cat_diagram_reconstruction_to C C1 (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@one_cat_square_diagram_transf C C1 (@fapp0 K C A x) (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@id C (@fapp0 K C A x)) (@id C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x)
  walking_arrow_src)) (@path_to_hom (Hom_cat C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@eq_sym (Hom C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x)
  walking_arrow_src)) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@zero_arrow_family_point_generator_path K C C1 t T A D h x))))
  (@one_cat_diagram_reconstruction_from C C1 (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))));

// The source component is the identity on the retained source object.
symbol zero_arrow_family_point_diagram_inverse_src_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj
  C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
    : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (@tapp0_fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_src (@zero_arrow_family_point_diagram_inverse K C C1
  t T A D h x)) (@id C (@fapp0 K C A x)))
≔ @eq_refl (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (@id C (@fapp0 K C A x));

// The target component is the identity on the retained target object.
symbol zero_arrow_family_point_diagram_inverse_tgt_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj
  C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
    : τ (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) walking_arrow_tgt (@zero_arrow_family_point_diagram_inverse K C C1
  t T A D h x)) (@id C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)))
≔ @eq_refl (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@id C (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src));

// The first composite is identity by ordinary diagram faithfulness.
symbol zero_arrow_family_point_diagram_left_law [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
     : τ (@= (@Transf WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@zero_arrow_family_point_diagram_inverse K C C1 t T A D h x)
  (@zero_arrow_family_point_diagram_map K C C1 t T A D h x)) (@id (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat
  WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x)))
≔ @one_cat_diagram_map_path C C1 (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 K
  (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@zero_arrow_family_point_diagram_inverse K C C1 t T A D h x)
  (@zero_arrow_family_point_diagram_map K C C1 t T A D h x)) (@id (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat
  WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x))
  (@eq_refl (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (@id C (@fapp0 K C A x))) (@eq_refl (Hom C (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src) (@fapp0 WalkingArrow_cat
  C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src)) (@id C (@fapp0 WalkingArrow_cat C
  (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src)));

// The reverse composite is identity by the same whole reconstruction.
symbol zero_arrow_family_point_diagram_right_law [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
     : τ (@= (@Transf WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x)
  (@zero_arrow_family_point_diagram_inverse K C C1 t T A D h x)) (@id (Functor_cat WalkingArrow_cat C) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x))))
≔ @one_cat_diagram_map_path C C1 (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x)
  (@zero_arrow_family_point_diagram_inverse K C C1 t T A D h x)) (@id (Functor_cat WalkingArrow_cat C) (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
  (@eq_refl (Hom C (@fapp0 K C A x) (@fapp0 K C A x)) (@id C (@fapp0 K C A x))) (@eq_refl (Hom C (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src) (@fapp0 WalkingArrow_cat
  C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src)) (@id C (@fapp0 WalkingArrow_cat C
  (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src)));

// Fixed-forward equivalence retains the derived inverse and both laws.
symbol zero_arrow_family_point_diagram_equiv [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
     : τ (@OmegaEquivAlong (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x))
≔ @omega_equiv_along_intro (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)) (@zero_arrow_family_point_diagram_map K C C1 t T A D h x)
  (@zero_arrow_family_point_diagram_inverse K C C1 t T A D h x) (@zero_arrow_family_point_diagram_inverse K C C1 t T A D h x)
  (@zero_arrow_family_point_diagram_left_law K C C1 t T A D h x) (@zero_arrow_family_point_diagram_right_law K C C1 t T A D h x);
