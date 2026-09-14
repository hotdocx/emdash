/* Point observations of the original whole incoming recovery. */
require open emdash.emdash3_2_one_cat_kernel_family_inputs;
require open emdash.emdash3_2_zero_arrow_diagram_observations;

// Evaluation commutes with the existing source observation.
symbol zero_arrow_family_point_incoming_path [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D))
  (x : τ (Obj K))
  : τ (@= (Hom C (@fapp0 K C X x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@terminal_arrow_test_incoming C t T (@fapp0 K C X x) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D x h)) (@tapp0_fapp0 K C X
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x (@sym_transf_tapp0_transf K
  WalkingArrow_cat C (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  X) D h walking_arrow_src)))
≔ @eq_refl (Hom C (@fapp0 K C X x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@terminal_arrow_test_incoming C t T (@fapp0 K C X x) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D x h));

// Derive the point law by observing the whole recovery path.
symbol one_cat_kernel_family_point_incoming_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
  (Functor_cat K C) X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf K WalkingArrow_cat
  C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf K C t T T0
  X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt))))
  (x : τ (Obj K))
  : τ (@= (Hom C (@fapp0 K C X x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@terminal_arrow_test_incoming C t T (@fapp0 K C X x) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D x (@one_cat_kernel_family_input K C C1 t T T0 X
  D k z))) (@tapp0_fapp0 K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x k))
≔ @eq_trans (Hom C (@fapp0 K C X x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x)
  walking_arrow_src)) (@terminal_arrow_test_incoming C t T (@fapp0 K C X x) (@fapp0 K (Functor_cat
  WalkingArrow_cat C) D x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) D x (@one_cat_kernel_family_input K C C1 t T T0 X
  D k z))) (@tapp0_fapp0 K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x
  (@sym_transf_tapp0_transf K WalkingArrow_cat C (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D (@one_cat_kernel_family_input K C C1 t T T0 X D k z)
  walking_arrow_src)) (@tapp0_fapp0 K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x
  k) (@zero_arrow_family_point_incoming_path K C t T X D (@one_cat_kernel_family_input K C C1 t T T0 X D k z) x)
  (@eq_ap (@Transf K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)) (Hom C (@fapp0 K C
  X x) (@fapp0 WalkingArrow_cat C (@fapp0 K (Functor_cat WalkingArrow_cat C) D x) walking_arrow_src)) (λ a : τ
  (@Transf K C X (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)), (@tapp0_fapp0 K C X
  (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x a)) (@sym_transf_tapp0_transf K
  WalkingArrow_cat C (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  X) D (@one_cat_kernel_family_input K C C1 t T T0 X D k z) walking_arrow_src) k
  (@one_cat_kernel_family_input_source_path K C C1 t T T0 X D k z));
