/* Zero preservation of the original whole product and coproduct mates. */
require open emdash.emdash3_2_one_cat_biproduct_family_distribution;
require open emdash.emdash3_2_one_cat_zero_family_postcomposition_paths;

// The original whole product mate sends the pair of zero transformations to zero.
symbol one_cat_product_family_pair_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X F G : τ (Functor K C))
  : τ (@= (@Transf K C X (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)))
  (@one_cat_product_family_pair K C C1 Prod (@additive_binary_products C Prod t Add) X F G
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X F)
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X G))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) F G))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@one_cat_product_pair_precompose_path K C C1 Prod
  (@additive_binary_products C Prod t Add) X X F G (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X X) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X F) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X G)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C X F) (@Transf K C
  X (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C
  Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G))) (λ v : τ (@Transf K C X F),
  (@one_cat_product_family_pair K C C1 Prod (@additive_binary_products C Prod t Add) X F G v (@comp_fapp0
  (Functor_cat K C) X X G (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X
  G) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X X)))) _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 X X F
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X X))) (@eq_ap (@Transf K
  C X G) (@Transf K C X (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G))) (λ v : τ
  (@Transf K C X G), (@one_cat_product_family_pair K C C1 Prod (@additive_binary_products C Prod t Add) X F G
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X F) v)) _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 X X G
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X X))))))
  (@one_cat_zero_family_postcompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 X X (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) (@one_cat_product_family_pair K C C1
  Prod (@additive_binary_products C Prod t Add) X F G (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X F) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X G))));

// The original whole coproduct mate sends the pair of zero transformations to zero.
symbol one_cat_copair_family_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G Z : τ (Functor K C))
  : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Z)
  (@one_cat_copair_family K C C1 Prod t Add T0 F G Z (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 F Z) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 G Z)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Z))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@one_cat_copair_postcompose_path K C C1 Prod t Add T0
  F
  G Z Z (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 F Z)
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 G Z)
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 Z Z)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C F Z) (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Z) (λ v : τ (@Transf K C F Z), (@one_cat_copair_family K C C1 Prod t Add T0 F G Z v (@comp_fapp0
  (Functor_cat K C) G Z Z (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 Z
  Z) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 G Z)))) _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 F Z Z
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 F Z))) (@eq_ap (@Transf K
  C G Z) (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Z) (λ v :
  τ (@Transf K C G Z), (@one_cat_copair_family K C C1 Prod t Add T0 F G Z (@zero_arrow_family_zero_transf K C
  t (@additive_terminal_object C Prod t Add) T0 F Z) v)) _ _ (@one_cat_zero_family_precompose_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 G Z Z (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 G Z)))))) (@one_cat_zero_family_precompose_path K C C1 t
  (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Z Z (@one_cat_copair_family K C C1 Prod t Add T0 F G Z (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 F Z) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 G Z))));

// Whole pairing preserves a common annihilator, by the original mate distribution.
symbol one_cat_product_pair_precompose_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y F G : τ (Functor K C)) (u : τ (@Transf K C X Y))
  (f : τ (@Transf K C Y F)) (g : τ (@Transf K C Y G))
  (p : τ (@= (@Transf K C X F) (@comp_fapp0 (Functor_cat K C) X Y F f u) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X F)))
  (q : τ (@= (@Transf K C X G) (@comp_fapp0 (Functor_cat K C) X Y G g u) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X G)))
  : τ (@= (@Transf K C X (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)))
  (@comp_fapp0 (Functor_cat K C) X Y (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) (@one_cat_product_family_pair K C C1 Prod (@additive_binary_products C Prod t Add) Y F G f g) u)
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 X (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) F G))))
≔ (@eq_trans _ _ _ _ (@one_cat_product_pair_precompose_path K C C1 Prod (@additive_binary_products C Prod t
  Add)
  X Y F G u f g) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C X F) (@Transf K C X (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) F G))) (λ v : τ (@Transf K C X F), (@one_cat_product_family_pair K
  C C1 Prod (@additive_binary_products C Prod t Add) X F G v (@comp_fapp0 (Functor_cat K C) X Y G g u))) _ _
  p) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C X G) (@Transf K C X (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) F G))) (λ v : τ (@Transf K C X G), (@one_cat_product_family_pair K C C1 Prod
  (@additive_binary_products C Prod t Add) X F G (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 X F) v)) _ _ q) (@one_cat_product_family_pair_zero_path K C C1
  Prod t Add T0 X F G))));

// Whole copairing preserves a common annihilator, by the original inverse-mate distribution.
symbol one_cat_copair_postcompose_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G X Y : τ (Functor K C))
  (f : τ (@Transf K C F X)) (g : τ (@Transf K C G X)) (u : τ (@Transf K C X Y))
  (p : τ (@= (@Transf K C F Y) (@comp_fapp0 (Functor_cat K C) F X Y u f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 F Y)))
  (q : τ (@= (@Transf K C G Y) (@comp_fapp0 (Functor_cat K C) G X Y u g) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 G Y)))
  : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y)
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) X Y u (@one_cat_copair_family K C C1 Prod t Add T0 F G X f g)) (@zero_arrow_family_zero_transf K
  C t (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Y))
≔ (@eq_trans _ _ _ _ (@one_cat_copair_postcompose_path K C C1 Prod t Add T0 F G X Y f g u) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C F Y) (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Y) (λ v : τ (@Transf K C F Y), (@one_cat_copair_family K C C1 Prod t Add T0 F G Y v (@comp_fapp0
  (Functor_cat K C) G X Y u g))) _ _ p) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C G Y) (@Transf K C (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y) (λ v : τ (@Transf K C G Y),
  (@one_cat_copair_family K C C1 Prod t Add T0 F G Y (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 F Y) v)) _ _ q) (@one_cat_copair_family_zero_path K C C1 Prod t
  Add T0 F G Y))));
