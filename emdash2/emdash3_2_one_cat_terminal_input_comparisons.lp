/* Comparison at the original diagram. Incoming observations determine the
   whole ordinary input; the terminal tips are equal by existing uniqueness. */
require open emdash.emdash3_2_one_cat_zero_cone_fibre_inclusion;
require open emdash.emdash3_2_one_cat_diagram_map_paths;
require open emdash.emdash3_2_zero_arrow_diagram_observations;

// Ordinary reflection retains both original transformations and their diagram.
symbol one_cat_terminal_input_comparison_path [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Obj C)) (D : τ (Functor WalkingArrow_cat C))
  (h k : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) X) D))
  (incoming : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C D walking_arrow_src)) (@terminal_arrow_test_incoming C t
  T X D h) (@terminal_arrow_test_incoming C t T X D k)))
  : τ (@= (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
  t T) X) D) h k)
≔ @one_cat_diagram_map_path C C1 (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  X) D h k incoming (@eq_trans (Hom C t (@fapp0 WalkingArrow_cat C D walking_arrow_tgt))
  (@terminal_arrow_test_tip C t T X D h) (@preadditive_hom_zero C S t (@fapp0 WalkingArrow_cat C D
  walking_arrow_tgt)) (@terminal_arrow_test_tip C t T X D k) (@preadditive_terminal_to_zero_path C S t (@fapp0
  WalkingArrow_cat C D walking_arrow_tgt) T (@terminal_arrow_test_tip C t T X D h)) (@eq_sym (Hom C t (@fapp0
  WalkingArrow_cat C D walking_arrow_tgt)) (@terminal_arrow_test_tip C t T X D k) (@preadditive_hom_zero C S t
  (@fapp0 WalkingArrow_cat C D walking_arrow_tgt)) (@preadditive_terminal_to_zero_path C S t (@fapp0
  WalkingArrow_cat C D walking_arrow_tgt) T (@terminal_arrow_test_tip C t T X D k))));

// Apply the existing whole fibre inclusion to that comparison.
symbol one_cat_terminal_input_comparison_map [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Obj C)) (D : τ (Functor WalkingArrow_cat C))
  (h k : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) X) D))
  (incoming : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C D walking_arrow_src)) (@terminal_arrow_test_incoming C t
  T X D h) (@terminal_arrow_test_incoming C t T X D k)))
  : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T X D h) (@zero_arrow_cone_obj C t T X D k))
≔ @fapp1_fapp0 (@Transf_cat WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D) (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_fibre_inclusion_func C
  C1 t T X D) h k (@path_to_hom (@Transf_cat WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D) h k (@one_cat_terminal_input_comparison_path C S C1 t T X D h k
  incoming));

// Preserve the original forward map and selected inverse.
symbol one_cat_terminal_input_comparison_equiv [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Obj C)) (D : τ (Functor WalkingArrow_cat C))
  (h k : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) X) D))
  (incoming : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C D walking_arrow_src)) (@terminal_arrow_test_incoming C t
  T X D h) (@terminal_arrow_test_incoming C t T X D k)))
  : τ (@OmegaEquivAlong (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T X D h) (@zero_arrow_cone_obj C t
  T X D k) (@one_cat_terminal_input_comparison_map C S C1 t T X D h k incoming))
≔ @omega_equiv_along_fapp1_fapp0 (@Transf_cat WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D) (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_fibre_inclusion_func C
  C1 t T X D) h k (@path_to_hom (@Transf_cat WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D) h k (@one_cat_terminal_input_comparison_path C S C1 t T X D h k
  incoming)) (@object_path_equiv_along (@Transf_cat WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat
  C) (@terminal_arrow_diagram_func C t T) X) D) h k (@one_cat_terminal_input_comparison_path C S C1 t T X D h k
  incoming));
