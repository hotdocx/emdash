/* Diagonal product reindex views for the same original functor chain. */
require open emdash.emdash3_2_product_family_reindex;
require open emdash.emdash3_2_one_cat_action_paths;

// This comparison is ordinary associativity plus the existing identity-family
// postcomposition path; it imposes no strictness on Prod, Q or H.
symbol product_diagonal_composition_path [K B C : Cat]
  (Prod : τ (Functor (Product_cat C C) C)) (Q : τ (Functor B C)) (H : τ (Functor K B))
  : τ (@= (Functor K C) (@comp_fapp0 Cat_cat K B C (@comp_fapp0 Cat_cat B C C (@comp_fapp0 Cat_cat C (Product_cat C C) C Prod (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C))) Q) H) (@comp_fapp0 Cat_cat K (Product_cat C C) C Prod (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H))))
≔ @eq_trans (Functor K C) (@comp_fapp0 Cat_cat K B C (@comp_fapp0 Cat_cat B C C (@comp_fapp0 Cat_cat C (Product_cat C C) C Prod (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C))) Q) H) (@comp_fapp0 Cat_cat K C C (@comp_fapp0 Cat_cat C (Product_cat C C) C Prod (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C))) (@comp_fapp0 Cat_cat K B C Q H)) (@comp_fapp0 Cat_cat K (Product_cat C C) C Prod (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H)))
    (@eq_sym _ _ _ (@comp_assoc Cat_cat K B C C (@comp_fapp0 Cat_cat C (Product_cat C C) C Prod (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C))) Q H))
    (@eq_trans (Functor K C) (@comp_fapp0 Cat_cat K C C (@comp_fapp0 Cat_cat C (Product_cat C C) C Prod (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C))) (@comp_fapp0 Cat_cat K B C Q H)) (@comp_fapp0 Cat_cat K (Product_cat C C) C Prod (@comp_fapp0 Cat_cat K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H))) (@comp_fapp0 Cat_cat K (Product_cat C C) C Prod (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H)))
      (@eq_sym _ _ _ (@comp_assoc Cat_cat K C (Product_cat C C) C Prod (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H)))
      (@eq_ap (Functor K (Product_cat C C)) (Functor K C)
        (λ v : τ (Functor K (Product_cat C C)), @comp_fapp0 Cat_cat K (Product_cat C C) C Prod v)
        (@comp_fapp0 Cat_cat K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H)) (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H))
        (@comp_postcomp_path Cat_cat K C (Product_cat C C) (@Struct_sigma (Functor C C) (λ _ : τ (Functor C C), Functor C C) (@id_func C) (@id_func C)) (@comp_fapp0 Cat_cat K B C Q H))));

// Sufficient whole-functor comparison for this diagonal composite only.
// Retain the literal composite Q∘H and compare every category and factor.
// The path above proves the agreement; this is not runtime reassociation.
unif_rule
  @comp_fapp0 Cat_cat $K $B $C
    (@comp_fapp0 Cat_cat $B $C $C
      (@comp_fapp0 Cat_cat $C (Product_cat $C $C) $C $Prod
        (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C))) $Q) $H
  ≡ @comp_fapp0 Cat_cat $K1 (Product_cat $C1 $C1) $C1 $Prod1
    (@hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $K1 $C1 (Product_cat $C1 $C1)
      (Struct_sigma (@id Cat_cat $C1) (@id Cat_cat $C1))
      (@comp_fapp0 Cat_cat $K1 $B1 $C1 $Q1 $H1))
  ↪ [ $K1 ≡ $K; $B1 ≡ $B; $C1 ≡ $C;
      $Prod1 ≡ $Prod; $Q1 ≡ $Q; $H1 ≡ $H ];
