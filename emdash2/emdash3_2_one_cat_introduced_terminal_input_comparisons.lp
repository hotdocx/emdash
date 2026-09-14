/* Stage canonical introduced-point comparison before specializing raw rows. */
require open emdash.emdash3_2_one_cat_terminal_input_comparisons;
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;

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
≔ @one_cat_terminal_input_comparison_map C S C1 t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero) incoming;

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
≔ @one_cat_terminal_input_comparison_equiv C S C1 t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h (@terminal_zero_composite_transf C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero) incoming;
