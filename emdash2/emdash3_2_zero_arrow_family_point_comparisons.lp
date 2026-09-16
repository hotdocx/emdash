/* Compare the original whole incoming observation with its native point input.
   Existing parent-presentation and introduced-diagram paths retain all data. */
require open emdash.emdash3_2_one_cat_kernel_input_pair_observations;
require open emdash.emdash3_2_one_cat_kernel_family_point_paths;
require open emdash.emdash3_2_zero_arrow_family_point_inputs;
require open emdash.emdash3_2_one_cat_zero_cones;
// Compare the whole parent presentations before evaluating the incoming arrow.
symbol zero_arrow_incoming_at_point_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
  : τ (@= (Hom C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@tapp0_fapp0 K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x
  (@zero_arrow_family_incoming_transf K C t T A D h)) (@terminal_arrow_test_incoming C t T (@fapp0 K C A x)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D x h)))
≔ @eq_trans _ _ _ _
    (@eq_ap (@Transf K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)) (Hom C (@fapp0 K
  C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src))
      (λ u : τ (@Transf K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)), @tapp0_fapp0
  K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x u) _ _
      (@zero_arrow_family_incoming_presentation_path K C t T A D h))
    (@eq_sym _ _ _ (@zero_arrow_family_point_incoming_path K C t T A D h x));

// Introduce the same evaluated incoming arrow as a walking-arrow diagram.
symbol zero_arrow_incoming_point_diagram_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj
  C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
  : τ (@= (Functor WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@walking_arrow_func C (@fapp0 K C A x) (@fapp0
  WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src)
  (@terminal_arrow_test_incoming C t T (@fapp0 K C A x) (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D x h))))
≔ @eq_trans _ _ _ _
    (@transf_arrow_diagram_point_path K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@zero_arrow_family_incoming_transf K C t T A D h) x)
    (@eq_ap (Hom C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (Functor WalkingArrow_cat C)
      (λ f : τ (Hom C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D
  x) walking_arrow_src)), @walking_arrow_func C (@fapp0 K C A x) (@fapp0 WalkingArrow_cat C (@fapp0 K
  (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src) f) _ _
      (@zero_arrow_incoming_at_point_path K C C1 t T A D h x));

// Both diagram observations meet at the same original point input.
symbol zero_arrow_global_incoming_point_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj K))
  : τ (@= (Functor WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_family_incoming_func K C t T A D h) x) (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_family_incoming_func (@ZeroArrowCone_cat C t T) C t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T)) (@zero_arrow_family_point_input K C t T A D h x)))
≔ @eq_trans _ _ _ _
    (@zero_arrow_incoming_point_diagram_path K C C1 t T A D h x)
    (@eq_sym _ _ _ (@zero_arrow_incoming_point_diagram_path (@ZeroArrowCone_cat C t T) C C1 t T
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C
  C1 t T) (@zero_arrow_family_point_input K C t T A D h x)));
