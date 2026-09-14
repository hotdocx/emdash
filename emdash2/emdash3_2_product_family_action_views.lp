require open emdash.emdash3_2_product_family_views;

/* Proof-time whole Hom-action view; neither runtime owner is unfolded. */

// Postcomposition with the product diagonal duplicates the entire original Hom action.
unif_rule @hom_postcomp_fapp1_func _ _ (@id Cat_cat Cat_cat) $B $C _
    (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $X $Y
  ≡ @Struct_sigma _ _ (@id Cat_cat $H1) (@id Cat_cat $H2)
  ↪ [ $H1 ≡ @Transf_cat $B $C $X $Y; $H2 ≡ @Transf_cat $B $C $X $Y ];

// Identity evaluation at proof-time-equal transformation Hom presentations.
// The native source/target and the original input are explicit obligations.
unif_rule @fapp0 $Source $Target (@id Cat_cat (@Transf_cat $B $C $F $G)) $h
  ≡ $k
  ↪ [ $Source ≡ @Transf_cat $B $C $F $G;
      $Target ≡ @Transf_cat $B $C $F $G; $h ≡ $k ];

// Native counterpart of the existing raw projected-composition views.
// Both original functors and all retained category parameters are compared.
unif_rule @sigma_Fst _ _
    (@hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $B $A (Product_cat $C _) $H $F)
  ≡ @hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $B0 $A0 $C0 $H0 $F0
  ↪ [ $B ≡ $B0; $A ≡ $A0; $C ≡ $C0; sigma_Fst $H ≡ $H0; $F ≡ $F0 ];
unif_rule @sigma_Snd _ _
    (@hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $B $A (Product_cat _ $C) $H $F)
  ≡ @hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $B0 $A0 $C0 $H0 $F0
  ↪ [ $B ≡ $B0; $A ≡ $A0; $C ≡ $C0; sigma_Snd $H ≡ $H0; $F ≡ $F0 ];

// Same whole composite and same two arrows; compare only retained endpoint presentations.
// Repeated arrow operands prevent this view from selecting an associativity orientation.
unif_rule @comp_fapp0 (Functor_cat $B $C) $X $Y $Z $g $f
  ≡ @comp_fapp0 (Functor_cat $B0 $C0) $X0 $Y0 $Z0 $g $f
  ↪ [ $B ≡ $B0; $C ≡ $C0; $X ≡ $X0; $Y ≡ $Y0; $Z ≡ $Z0 ];

symbol diagonal_family_action_path [B C : Cat]
  (X Y : τ (Functor B C))
  : τ (@= (Functor (@Transf_cat B C X Y)
        (Hom_cat (Functor_cat B (Product_cat C C))
          (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
            (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
          (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
            (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))
      (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C))
        (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y)
      (@product_diagonal_func (@Transf_cat B C X Y)))
≔ @eq_refl (Functor (@Transf_cat B C X Y)
      (Hom_cat (Functor_cat B (Product_cat C C))
        (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
          (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
        (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
          (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))
    (@product_diagonal_func (@Transf_cat B C X Y));


/* Keep literal native Sigma/Hom parameters in diagonal action observations. */

symbol diagonal_family_native_proj1_path [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ
  (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h)) h)
≔ @eq_ap (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Y))) (@Transf B C X Y)
    (λ K : τ (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Y))), (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ
  _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp0 (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Y)) K h)))
    (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X Y) (@product_diagonal_func (@Transf_cat B C X Y)) (@diagonal_family_action_path
  B C X Y);

symbol diagonal_family_native_proj2_path [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ
  (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h)) h)
≔ @eq_ap (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Y))) (@Transf B C X Y)
    (λ K : τ (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Y))), (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ
  _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp0 (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Y)) K h)))
    (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X Y) (@product_diagonal_func (@Transf_cat B C X Y)) (@diagonal_family_action_path
  B C X Y);
