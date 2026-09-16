/* Actual diagram endpoints and inverse data; no diagram-object identification. */
require open emdash.emdash3_2_one_cat_introduced_terminal_input_comparisons;

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C
  t T A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h)
  (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u)
  zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h incoming)) ≡
  (@id C A);

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) (@zero_composite_native_cone C S C1 t T
  A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero)
  (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h incoming)) ≡
  (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming);

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func
  K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u))
  walking_arrow_src (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming)) ≡ (@id C
  (@fapp0 K C F x));

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@tapp0_fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func
  K C F G u) x) (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u))
  walking_arrow_tgt (@introduced_input_diagram_map K C S C1 t T F G u x A b zero h incoming)) ≡ (@id C
  (@fapp0 K C G x));

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u)
  zero) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@omega_equiv_along_left_inv (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C
  F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0
  K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h
  incoming) (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t T F G u x A b zero h
  incoming))) ≡ (@id C A);

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0
  K C G x) b (@tapp0_fapp0 K C F G x u) zero) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) (@omega_equiv_along_left_inv
  (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K
  C S C1 t T F G u x A b zero h incoming) (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t
  T F G u x A b zero h incoming))) ≡ (@omega_equiv_along_left_inv (Functor_cat WalkingArrow_cat C) (@fapp0
  K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C
  (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u)) (@introduced_input_diagram_map K C S C1 t
  T F G u x A b zero h incoming) (@introduced_input_diagram_equiv K C S C1 t T F G u x A b zero h
  incoming));

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u)
  zero) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@omega_equiv_along_right_inv (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C
  F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0
  K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h
  incoming) (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t T F G u x A b zero h
  incoming))) ≡ (@id C A);

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0
  K C G x) b (@tapp0_fapp0 K C F G x u) zero) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h) (@omega_equiv_along_right_inv
  (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K
  C S C1 t T F G u x A b zero h incoming) (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t
  T F G u x A b zero h incoming))) ≡ (@omega_equiv_along_left_inv (Functor_cat WalkingArrow_cat C) (@fapp0
  K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) (@walking_arrow_func C
  (@fapp0 K C F x) (@fapp0 K C G x) (@tapp0_fapp0 K C F G x u)) (@introduced_input_diagram_map K C S C1 t
  T F G u x A b zero h incoming) (@introduced_input_diagram_equiv K C S C1 t T F G u x A b zero h
  incoming));

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@omega_equiv_along_left_law (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h)
  (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u)
  zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h incoming)
  (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t T F G u x A b zero h incoming)) : τ (@=
  (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat
  WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h)) (@comp_fapp0 (@ZeroArrowCone_cat C t
  T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func
  K C F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b
  (@tapp0_fapp0 K C F G x u) zero) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat
  C) (@transf_arrow_diagram_func K C F G u) x) h) (@omega_equiv_along_left_inv (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C
  F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0
  K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h
  incoming) (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t T F G u x A b zero h
  incoming)) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h incoming))
  (@id (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h)));

assert [K C : Cat] (S : τ (@PreadditiveCategory C))
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
 ⊢ (@omega_equiv_along_right_law (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T A (@fapp0 K
  (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C F G u) x) h)
  (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u)
  zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h incoming)
  (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t T F G u x A b zero h incoming)) : τ (@=
  (Hom (@ZeroArrowCone_cat C t T) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G
  x) b (@tapp0_fapp0 K C F G x u) zero) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0
  K C G x) b (@tapp0_fapp0 K C F G x u) zero)) (@comp_fapp0 (@ZeroArrowCone_cat C t T)
  (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u)
  zero) (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K
  C S C1 t T F G u x A b zero h incoming) (@omega_equiv_along_right_inv (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t T A (@fapp0 K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C
  F G u) x) h) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x) (@fapp0 K C G x) b (@tapp0_fapp0
  K C F G x u) zero) (@one_cat_introduced_terminal_input_comparison_map K C S C1 t T F G u x A b zero h
  incoming) (@one_cat_introduced_terminal_input_comparison_equiv K C S C1 t T F G u x A b zero h
  incoming))) (@id (@ZeroArrowCone_cat C t T) (@zero_composite_native_cone C S C1 t T A (@fapp0 K C F x)
  (@fapp0 K C G x) b (@tapp0_fapp0 K C F G x u) zero)));
