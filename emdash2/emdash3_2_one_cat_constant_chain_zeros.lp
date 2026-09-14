/* Whole constant-chain zeros through existing weakening and categorical uniqueness. */
require open emdash.emdash3_2_one_cat_constant_transformation_views;
require open emdash.emdash3_2_one_cat_cokernel_family_inputs;
require open emdash.emdash3_2_additive_categories;

// The original whole zero is the same terminal/initial factorization.
symbol one_cat_constant_zero_factor_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C))
  : τ (@= (@Transf K C (@Const_func K C x) (@Const_func K C y)) (@comp_fapp0 (Functor_cat K C) (@Const_func K C
  x) (@Const_func K C t) (@Const_func K C y) (@Const_transf K C t y (@preadditive_hom_zero C S t y))
  (@Const_transf K C x t (@terminal_arrow_fapp0 C t T x))) (@zero_arrow_family_zero_transf K C t T T0
  (@Const_func K C x) (@Const_func K C y)))
≔ (@eq_trans (@Transf K C (@Const_func K C x) (@Const_func K C y)) (@comp_fapp0 (Functor_cat K C) (@Const_func K
  C x) (@Const_func K C t) (@Const_func K C y) (@Const_transf K C t y (@preadditive_hom_zero C S t y))
  (@Const_transf K C x t (@terminal_arrow_fapp0 C t T x))) (@comp_fapp0 (Functor_cat K C) (@Const_func K C x)
  (@Const_func K C t) (@Const_func K C y) (@diagram_family_transf K WalkingArrow_cat C (@comp_cat_fapp0 K C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@Const_func K C y)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@Const_transf K C x t (@terminal_arrow_fapp0 C t T x)))
  (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C y)) (@eq_ap (@Transf K C
  (@Const_func K C t) (@Const_func K C y)) (@Transf K C (@Const_func K C x) (@Const_func K C y)) (λ u : τ
  (@Transf K C (@Const_func K C t) (@Const_func K C y)), (@comp_fapp0 (Functor_cat K C) (@Const_func K C x)
  (@Const_func K C t) (@Const_func K C y) u (@Const_transf K C x t (@terminal_arrow_fapp0 C t T x))))
  (@Const_transf K C t y (@preadditive_hom_zero C S t y)) (@diagram_family_transf K WalkingArrow_cat C
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@Const_func K C
  y)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@one_cat_initial_family_arrow_path K C C1 t
  T0 (@Const_func K C y) (@Const_transf K C t y (@preadditive_hom_zero C S t y)))) (@eq_ap (@Transf K C
  (@Const_func K C x) (@Const_func K C t)) (@Transf K C (@Const_func K C x) (@Const_func K C y)) (λ u : τ
  (@Transf K C (@Const_func K C x) (@Const_func K C t)), (@comp_fapp0 (Functor_cat K C) (@Const_func K C x)
  (@Const_func K C t) (@Const_func K C y) (@diagram_family_transf K WalkingArrow_cat C (@comp_cat_fapp0 K C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@Const_func K C y)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) u)) (@Const_transf K C x t (@terminal_arrow_fapp0 C t T x))
  (@diagram_family_transf K WalkingArrow_cat C (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@Const_func K C x)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@one_cat_terminal_family_arrow_path K C C1 t T (@Const_func K C x) (@Const_transf K
  C x t (@terminal_arrow_fapp0 C t T x)))));

// The constant additive zero agrees as a whole transformation with the native zero.
symbol one_cat_constant_family_zero_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj C))
  : τ (@= (@Transf K C (@Const_func K C x) (@Const_func K C y)) (@Const_transf K C x y (@preadditive_hom_zero C
  S x y)) (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C y)))
≔ (@eq_trans (@Transf K C (@Const_func K C x) (@Const_func K C y)) (@Const_transf K C x y (@preadditive_hom_zero
  C S x y)) (@comp_fapp0 (Functor_cat K C) (@Const_func K C x) (@Const_func K C t) (@Const_func K C y)
  (@Const_transf K C t y (@preadditive_hom_zero C S t y)) (@Const_transf K C x t (@terminal_arrow_fapp0 C t T
  x))) (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C y)) (@eq_trans (@Transf K
  C (@Const_func K C x) (@Const_func K C y)) (@Const_transf K C x y (@preadditive_hom_zero C S x y))
  (@Const_transf K C x y (@comp_fapp0 C x t y (@preadditive_hom_zero C S t y) (@terminal_arrow_fapp0 C t T x)))
  (@comp_fapp0 (Functor_cat K C) (@Const_func K C x) (@Const_func K C t) (@Const_func K C y) (@Const_transf K C
  t y (@preadditive_hom_zero C S t y)) (@Const_transf K C x t (@terminal_arrow_fapp0 C t T x))) (@eq_sym
  (@Transf K C (@Const_func K C x) (@Const_func K C y)) (@Const_transf K C x y (@comp_fapp0 C x t y
  (@preadditive_hom_zero C S t y) (@terminal_arrow_fapp0 C t T x))) (@Const_transf K C x y
  (@preadditive_hom_zero C S x y)) (@eq_ap (Hom C x y) (@Transf K C (@Const_func K C x) (@Const_func K C y)) (λ
  u : τ (Hom C x y), (@Const_transf K C x y u)) (@comp_fapp0 C x t y (@preadditive_hom_zero C S t y)
  (@terminal_arrow_fapp0 C t T x)) (@preadditive_hom_zero C S x y) (@preadditive_comp_zero_left_path C S x t y
  (@terminal_arrow_fapp0 C t T x)))) (@fapp1_comp_path C (Functor_cat K C) (@Const_func_func K C) x t y
  (@preadditive_hom_zero C S t y) (@terminal_arrow_fapp0 C t T x))) (@one_cat_constant_zero_factor_path K C S C1
  t T T0 x y));

// A raw chain-zero equation produces the whole constant-family chain-zero input.
symbol one_cat_constant_chain_zero_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [x y z : τ (Obj C)] (f : τ (Hom C x y)) (g : τ (Hom C y z))
  (p : τ (@= (Hom C x z) (@comp_fapp0 C x y z g f) (@preadditive_hom_zero C S x z)))
  : τ (@= (@Transf K C (@Const_func K C x) (@Const_func K C z)) (@comp_fapp0 (Functor_cat K C) (@Const_func K C
  x) (@Const_func K C y) (@Const_func K C z) (@Const_transf K C y z g) (@Const_transf K C x y f))
  (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C z)))
≔ (@eq_trans (@Transf K C (@Const_func K C x) (@Const_func K C z)) (@comp_fapp0 (Functor_cat K C) (@Const_func K
  C x) (@Const_func K C y) (@Const_func K C z) (@Const_transf K C y z g) (@Const_transf K C x y f))
  (@Const_transf K C x z (@comp_fapp0 C x y z g f)) (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C
  x) (@Const_func K C z)) (@eq_sym (@Transf K C (@Const_func K C x) (@Const_func K C z)) (@Const_transf K C x z
  (@comp_fapp0 C x y z g f)) (@comp_fapp0 (Functor_cat K C) (@Const_func K C x) (@Const_func K C y) (@Const_func
  K C z) (@Const_transf K C y z g) (@Const_transf K C x y f)) (@fapp1_comp_path C (Functor_cat K C)
  (@Const_func_func K C) x y z g f)) (@eq_trans (@Transf K C (@Const_func K C x) (@Const_func K C z))
  (@Const_transf K C x z (@comp_fapp0 C x y z g f)) (@Const_transf K C x z (@preadditive_hom_zero C S x z))
  (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C x) (@Const_func K C z)) (@eq_ap (Hom C x z)
  (@Transf K C (@Const_func K C x) (@Const_func K C z)) (λ u : τ (Hom C x z), (@Const_transf K C x z u))
  (@comp_fapp0 C x y z g f) (@preadditive_hom_zero C S x z) p) (@one_cat_constant_family_zero_path K C S C1 t T
  T0 x z)));
