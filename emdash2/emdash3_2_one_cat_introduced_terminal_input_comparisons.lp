/* Retain both original diagram presentations in the native input comparison. */
require open emdash.emdash3_2_one_cat_terminal_input_comparisons;
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;
require open emdash.emdash3_2_one_cat_diagram_map_equivalences;
require open emdash.emdash3_2_one_cat_zero_cone_map_equivalences;

// Reconstruct the evaluated diagram as its introduced generator, retaining actual endpoints.
symbol introduced_input_diagram_map [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F G : τ (Functor K C)) (u : τ (@Transf K C F G)) (x : τ (Obj K))
  (A : τ (Obj C))
  (b : τ (Hom C A (@fapp0 K C F x)))
  (zero : τ (@= (Hom C A (@fapp0 K C G x)) (@comp_fapp0 C A (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C
  F G x u) b) (@preadditive_hom_zero C S A (@fapp0 K C G x))))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x)))
  (incoming : τ (@= (Hom C A (@fapp0 K C F x)) (@terminal_arrow_test_incoming C t T A (@fapp0 K
  (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) b))
 : τ (@Transf WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K
  C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u)))
≔ @one_cat_original_diagram_map C C1 (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u)) (@id C (@fapp0 K C F x)) (@id C (@fapp0 K C G x))
 (@path_to_hom (Hom_cat C (@fapp0 K C F x) (@fapp0 K C G x)) (@fapp1_fapp0 WalkingArrow_cat C (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@tapp0_fapp0 K C F G x u) (@eq_refl (Hom C (@fapp0 K C F x)
  (@fapp0 K C G x)) (@tapp0_fapp0 K C F G x u)));

symbol introduced_input_diagram_equiv [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F G : τ (Functor K C)) (u : τ (@Transf K C F G)) (x : τ (Obj K))
  (A : τ (Obj C))
  (b : τ (Hom C A (@fapp0 K C F x)))
  (zero : τ (@= (Hom C A (@fapp0 K C G x)) (@comp_fapp0 C A (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C
  F G x u) b) (@preadditive_hom_zero C S A (@fapp0 K C G x))))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x)))
  (incoming : τ (@= (Hom C A (@fapp0 K C F x)) (@terminal_arrow_test_incoming C t T A (@fapp0 K
  (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) b))
 : τ (@OmegaEquivAlong (Functor_cat WalkingArrow_cat C) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u)) (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming))
≔ @one_cat_diagram_map_equiv C C1 (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K
  C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u))
  (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming)
 (@omega_equiv_along_refl C (@fapp0 K C F x)) (@omega_equiv_along_refl C (@fapp0 K C G x));

// Original incoming recovery and ordinary terminal uniqueness determine compatibility.
symbol introduced_input_diagram_compatibility [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F G : τ (Functor K C)) (u : τ (@Transf K C F G)) (x : τ (Obj K))
  (A : τ (Obj C))
  (b : τ (Hom C A (@fapp0 K C F x)))
  (zero : τ (@= (Hom C A (@fapp0 K C G x)) (@comp_fapp0 C A (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C
  F G x u) b) (@preadditive_hom_zero C S A (@fapp0 K C G x))))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x)))
  (incoming : τ (@= (Hom C A (@fapp0 K C F x)) (@terminal_arrow_test_incoming C t T A (@fapp0 K
  (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) b))
 : τ (@= (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u))) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u)) (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming) h)
  (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G
  x u) zero))
≔ @one_cat_diagram_map_path C C1 (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) A) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u))
  (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u)) (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming) h)
  (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G
  x u) zero) incoming
 (@eq_trans _ _ _ _
  (@preadditive_terminal_to_zero_path C S t (@fapp0 K C G x) T (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) (@walking_arrow_func C (@fapp0
  K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u)) walking_arrow_tgt (@comp_fapp0 (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
  (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x)
  (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u))
  (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming) h)))
  (@eq_sym _ _ _ (@preadditive_terminal_to_zero_path C S t (@fapp0 K C G x) T (@tapp0_fapp0
  WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
  (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u)) walking_arrow_tgt
  (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G
  x u) zero)))));

symbol one_cat_introduced_terminal_input_comparison_map [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F G : τ (Functor K C)) (u : τ (@Transf K C F G)) (x : τ (Obj K))
  (A : τ (Obj C))
  (b : τ (Hom C A (@fapp0 K C F x)))
  (zero : τ (@= (Hom C A (@fapp0 K C G x)) (@comp_fapp0 C A (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C
  F G x u) b) (@preadditive_hom_zero C S A (@fapp0 K C G x))))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
  t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x)))
  (incoming : τ (@= (Hom C A (@fapp0 K C F x)) (@terminal_arrow_test_incoming C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) b))
  : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero))
≔ @zero_cone_native_map C t T A A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K
  C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u)) h
  (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G
  x u) zero) (@id C A) (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming)
  (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u))) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u)) (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming) h)
  (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G
  x u) zero) (@introduced_input_diagram_compatibility K C S C1 t T F G u x A b zero h incoming));

symbol one_cat_introduced_terminal_input_comparison_equiv [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (F G : τ (Functor K C)) (u : τ (@Transf K C F G)) (x : τ (Obj K))
  (A : τ (Obj C))
  (b : τ (Hom C A (@fapp0 K C F x)))
  (zero : τ (@= (Hom C A (@fapp0 K C G x)) (@comp_fapp0 C A (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C
  F G x u) b) (@preadditive_hom_zero C S A (@fapp0 K C G x))))
  (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C
  t T) A) (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x)))
  (incoming : τ (@= (Hom C A (@fapp0 K C F x)) (@terminal_arrow_test_incoming C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) b))
  : τ (@OmegaEquivAlong (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) (@zero_composite_native_cone C S C1 t T A
  (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero)
  (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h incoming))
≔ @one_cat_zero_cone_map_equiv C C1 t T A A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
  (@tapp0_fapp0 K C F G x u)) h (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x) (@fapp0 K C
  G x) b (@tapp0_fapp0 K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T
  F G u x A b zero h incoming) (@omega_equiv_along_refl C A) (@introduced_input_diagram_equiv K C S C1 t T
  F G u x A b zero h incoming);
