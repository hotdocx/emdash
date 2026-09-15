/* Whole second-coordinate annihilation through the original uncopairing mate. */
require open emdash.emdash3_2_one_cat_biproduct_family_zeros;

// The original whole inverse mate retains both zero-composite coordinates.
symbol one_cat_uncopair_postcompose_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G X Y : τ (Functor K C)) (f : τ (@Transf K C F X))
  (g : τ (@Transf K C G X)) (u : τ (@Transf K C X Y))
  (p : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y)
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) X Y u (@one_cat_copair_family K C C1 Prod t Add T0 F G X f g)) (@zero_arrow_family_zero_transf K
  C t (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Y)))
  : τ (@= (@Product_grpd (@Transf K C F Y) (@Transf K C G Y)) (@Product_pair_grpd (@Transf K C F Y) (@Transf K
  C G Y) (@comp_fapp0 (Functor_cat K C) F X Y u f) (@comp_fapp0 (Functor_cat K C) G X Y u g))
  (@Product_pair_grpd (@Transf K C F Y) (@Transf K C G Y) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 F Y) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 G Y)))
≔ (@eq_ap (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y)
  (@Product_grpd (@Transf K C F Y) (@Transf K C G Y)) (λ v : τ (@Transf K C (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y), (@one_cat_uncopair_family K C C1 Prod t Add T0 F G Y v))
  _ _ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_copair_postcompose_path K C C1 Prod t Add T0 F G X Y f g u))
  (@eq_trans _ _ _ _ p (@eq_sym _ _ _ (@one_cat_copair_family_zero_path K C C1 Prod t Add T0 F G Y)))));

// If u∘[f,g]=0, the native inverse mate gives u∘g=0 at the original whole maps.
symbol one_cat_copair_postcompose_second_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G X Y : τ (Functor K C)) (f : τ (@Transf K C F X))
  (g : τ (@Transf K C G X)) (u : τ (@Transf K C X Y))
  (p : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y)
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) X Y u (@one_cat_copair_family K C C1 Prod t Add T0 F G X f g)) (@zero_arrow_family_zero_transf K
  C t (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Y)))
  : τ (@= (@Transf K C G Y) (@comp_fapp0 (Functor_cat K C) G X Y u g) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 G Y))
≔ (@eq_ap (@Product_grpd (@Transf K C F Y) (@Transf K C G Y)) (@Transf K C G Y) (λ v : τ (@Product_grpd
  (@Transf K C F Y) (@Transf K C G Y)), sigma_Snd v) _ _ (@one_cat_uncopair_postcompose_zero_path K C C1 Prod
  t Add T0 F G X Y f g u p));

// The same whole pair law yields the original first zero composite.
symbol one_cat_copair_postcompose_first_zero_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (F G X Y : τ (Functor K C)) (f : τ (@Transf K C F X))
  (g : τ (@Transf K C G X)) (u : τ (@Transf K C X Y))
  (p : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) F G)) Y)
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) X Y u (@one_cat_copair_family K C C1 Prod t Add T0 F G X f g)) (@zero_arrow_family_zero_transf K
  C t (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) F G)) Y)))
  : τ (@= (@Transf K C F Y) (@comp_fapp0 (Functor_cat K C) F X Y u f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 F Y))
≔ (@eq_ap (@Product_grpd (@Transf K C F Y) (@Transf K C G Y)) (@Transf K C F Y) (λ v : τ (@Product_grpd
  (@Transf K C F Y) (@Transf K C G Y)), sigma_Fst v) _ _ (@one_cat_uncopair_postcompose_zero_path K C C1 Prod
  t Add T0 F G X Y f g u p));
