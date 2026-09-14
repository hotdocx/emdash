require open emdash.emdash3_2_one_cat_adjunction_family_reindex;
require open emdash.emdash3_2_product_family_reindex;
require open emdash.emdash3_2_one_cat_copair_families;
require open emdash.emdash3_2_one_cat_additive_family_paths;

/* Restriction of the original native product and coproduct mate programs. */

// Both restricted coordinates feed the same original product mate.
symbol one_cat_product_pair_reindex_path [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (U : τ (Functor A B)) (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair B C C1 Prod BP X F G f g)) (@one_cat_product_family_pair A C C1 Prod BP
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@fapp0 (@Transf_cat B C X F)
  (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f)
  (@fapp0 (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X G) g)))
≔ (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
  (@one_cat_product_family_pair B C C1 Prod BP X F G f g)) (@fapp0 (Hom_cat (Functor_cat A (Product_cat C C)) (@fapp0
  (Functor_cat A C) (Functor_cat A (Product_cat C C)) (@comp_cat_cov_func A C (Product_cat C C)
  (@product_diagonal_func C)) (@comp_cat_fapp0 A B C X U)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)) (Hom_cat (Functor_cat A C) (@comp_cat_fapp0 A B C X U)
  (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod)
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)))
  (@one_cat_adjunction_family_transpose_func A C (Product_cat C C) C1 (@one_cat_product_category C C C1 C1)
  (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod BP) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U))
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Struct_sigma
  (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g))) (@one_cat_product_family_pair A C C1 Prod BP
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@fapp0 (@Transf_cat B C X F)
  (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f)
  (@fapp0 (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X G) g)) (@one_cat_transpose_reindex_path A B C (Product_cat C C) C1
  (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod
  BP) U X (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@Struct_sigma (@Transf B C X F) (λ _
  : τ (@Transf B C X F), @Transf B C X G) f g)) (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0
  (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma
  (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U))))
  (@fapp0 (Hom_cat (Functor_cat A (Product_cat C C)) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C))
  (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C X U)) (@comp_cat_fapp0
  A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)) (Hom_cat
  (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) F G) U))) (@one_cat_adjunction_family_transpose_func A C (Product_cat C C) C1
  (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod
  BP) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@comp_cat_fapp0
  B C (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G)) (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g))) (@fapp0 (Hom_cat
  (Functor_cat A (Product_cat C C)) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C)) (@comp_cat_cov_func A
  C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C X U)) (@comp_cat_fapp0 A B (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)) (Hom_cat (Functor_cat A C)
  (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A
  (Product_cat C C) C Prod) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G) U))) (@one_cat_adjunction_family_transpose_func A C (Product_cat C C) C1
  (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod
  BP) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) U)) (@Struct_sigma (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C
  F U)) (λ _ : τ (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)), @Transf A C (@comp_cat_fapp0 A
  B C X U) (@comp_cat_fapp0 A B C G U)) (@fapp0 (@Transf_cat B C X F) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f) (@fapp0 (@Transf_cat B C X G) (@Transf_cat A
  C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U)) (@comp_cat_con_fapp1_func A B C U X G) g)))
  (@one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)
  (@comp_cat_fapp0 A B C G U) (@fapp0 (@Transf_cat B C X F) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f) (@fapp0 (@Transf_cat B C X G) (@Transf_cat A
  C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U)) (@comp_cat_con_fapp1_func A B C U X G) g)) (@eq_ap (Obj
  (Hom_cat (Functor_cat A (Product_cat C C)) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C))
  (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C X U)) (@comp_cat_fapp0
  A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U))) (@Transf A C
  (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A
  (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F
  U) (@comp_cat_fapp0 A B C G U)))) (λ h : τ (Obj (Hom_cat (Functor_cat A (Product_cat C C)) (@fapp0 (Functor_cat A C)
  (Functor_cat A (Product_cat C C)) (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C))
  (@comp_cat_fapp0 A B C X U)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G) U))), (@fapp0 (Hom_cat (Functor_cat A (Product_cat C C)) (@fapp0 (Functor_cat A C)
  (Functor_cat A (Product_cat C C)) (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C))
  (@comp_cat_fapp0 A B C X U)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G) U)) (Hom_cat (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat
  C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@comp_cat_fapp0 A B (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)))
  (@one_cat_adjunction_family_transpose_func A C (Product_cat C C) C1 (@one_cat_product_category C C C1 C1)
  (@product_diagonal_func C) Prod (@one_cat_binary_product_adjunction C C1 Prod BP) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U))
  h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Struct_sigma
  (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g)) (@Struct_sigma (@Transf A C (@comp_cat_fapp0 A
  B C X U) (@comp_cat_fapp0 A B C F U)) (λ _ : τ (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F
  U)), @Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U)) (@fapp0 (@Transf_cat B C X F) (@Transf_cat
  A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f) (@fapp0
  (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X G) g)) (@mate_input_source_reindex_path A B C U X F G f g)) (@eq_refl
  (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U)))) (@one_cat_product_family_pair A C C1 Prod BP
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@fapp0 (@Transf_cat B C X F)
  (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) f)
  (@fapp0 (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X G) g)))));

// Restriction preserves whole copairing at the original selected product endpoint.
symbol one_cat_copair_reindex_path [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (V : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (U : τ (Functor A B)) (F G Y : τ (Functor B C))
  (f : τ (@Transf B C F Y)) (g : τ (@Transf B C G Y))
  : τ (@= (@Transf A C (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat
  C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F U)
  (@comp_cat_fapp0 A B C G U))) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  Y) (@one_cat_copair_family B C C1 Prod t V T0 F G Y f g)) (@one_cat_copair_family A C C1 Prod t V T0
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C F Y)
  (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y) f)
  (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U G Y) g)))
≔ (@eq_trans (@Transf A C (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A
  (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F
  U) (@comp_cat_fapp0 A B C G U))) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
  Y) (@one_cat_copair_family B C C1 Prod t V T0 F G Y f g)) (@fapp0 (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)
  (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C)) (@comp_cat_cov_func A C (Product_cat C C)
  (@product_diagonal_func C)) (@comp_cat_fapp0 A B C Y U))) (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat A
  (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@comp_cat_fapp0 A B
  (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)) (@comp_cat_fapp0 A B C
  Y U)) (@one_cat_adjunction_family_untranspose_func A (Product_cat C C) C (@one_cat_product_category C C C1 C1) C1
  Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t V T0) (@comp_cat_fapp0 A B (Product_cat C
  C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _
  _ (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y)) (@Struct_sigma (@Transf B C F Y) (λ _
  : τ (@Transf B C F Y), @Transf B C G Y) f g))) (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A B C F
  U) (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C F Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y) f) (@fapp0
  (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U G Y) g)) (@one_cat_untranspose_reindex_path A B (Product_cat C C) C
  (@one_cat_product_category C C C1 C1) C1 Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t
  V T0) U (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) Y (@Struct_sigma (@Transf B C F Y) (λ
  _ : τ (@Transf B C F Y), @Transf B C G Y) f g)) (@eq_trans (@Transf A C (@fapp0 (Functor_cat A (Product_cat C C))
  (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A
  C), Functor A C) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U))) (@comp_cat_fapp0 A B C Y U)) (@fapp0
  (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) F G) U) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C))
  (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C Y U))) (Hom_cat
  (Functor_cat A C) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C
  C) C Prod) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G) U)) (@comp_cat_fapp0 A B C Y U)) (@one_cat_adjunction_family_untranspose_func A (Product_cat C C) C
  (@one_cat_product_category C C C1 C1) C1 Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t
  V T0) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y)) (@Struct_sigma (@Transf B C F Y) (λ _ : τ (@Transf B C F Y), @Transf B C G Y) f g)))
  (@fapp0 (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C))
  (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C Y U))) (Hom_cat
  (Functor_cat A C) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C
  C) C Prod) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G) U)) (@comp_cat_fapp0 A B C Y U)) (@one_cat_adjunction_family_untranspose_func A (Product_cat C C) C
  (@one_cat_product_category C C C1 C1) C1 Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t
  V T0) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  U) (@comp_cat_fapp0 A B C Y U)) (@Struct_sigma (@Transf A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U))
  (λ _ : τ (@Transf A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)), @Transf A C (@comp_cat_fapp0 A B C G
  U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 (@Transf_cat B C F Y) (@Transf_cat A C (@comp_cat_fapp0 A B C F U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y) f) (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A
  C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U G Y) g)))
  (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0
  A B C Y U) (@fapp0 (@Transf_cat B C F Y) (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U F Y) f) (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U G Y) g)) (@eq_ap (Obj (Hom_cat (Functor_cat A
  (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) U) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C)) (@comp_cat_cov_func A C
  (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C Y U)))) (@Transf A C (@fapp0 (Functor_cat A
  (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ
  _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U))) (@comp_cat_fapp0 A B C Y
  U)) (λ h : τ (Obj (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C
  C)) (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C Y U)))), (@fapp0
  (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) F G) U) (@fapp0 (Functor_cat A C) (Functor_cat A (Product_cat C C))
  (@comp_cat_cov_func A C (Product_cat C C) (@product_diagonal_func C)) (@comp_cat_fapp0 A B C Y U))) (Hom_cat
  (Functor_cat A C) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C
  C) C Prod) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  F G) U)) (@comp_cat_fapp0 A B C Y U)) (@one_cat_adjunction_family_untranspose_func A (Product_cat C C) C
  (@one_cat_product_category C C C1 C1) C1 Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t
  V T0) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  U) (@comp_cat_fapp0 A B C Y U)) h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y)) (@Struct_sigma (@Transf B C F Y) (λ _ : τ (@Transf B C F Y), @Transf B C G Y) f g))
  (@Struct_sigma (@Transf A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)) (λ _ : τ (@Transf A C
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)), @Transf A C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A
  B C Y U)) (@fapp0 (@Transf_cat B C F Y) (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U F Y) f) (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U G Y) g)) (@mate_input_target_reindex_path A B C
  U F G Y f g)) (@eq_refl (@Transf A C (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func
  A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C
  F U) (@comp_cat_fapp0 A B C G U))) (@comp_cat_fapp0 A B C Y U)) (@one_cat_copair_family A C C1 Prod t V T0
  (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C F Y)
  (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y) f)
  (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U G Y) g)))));

/* Whole product diagonal and addition preserved under the original restrictions. */

// The same whole diagonal pairing is obtained after restriction.
symbol one_cat_product_diagonal_reindex_path [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (U : τ (Functor A B)) (X : τ (Functor B C))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)))
  (@one_cat_product_family_pair B C C1 Prod BP X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))
  (@one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)) (@id (Functor_cat A C)
  (@comp_cat_fapp0 A B C X U))))
≔ (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C C)) (Functor_cat A C)
  (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)))
  (@one_cat_product_family_pair B C C1 Prod BP X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))
  (@one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@fapp0 (@Transf_cat B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B C) X)) (@fapp0 (@Transf_cat
  B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U
  X X) (@id (Functor_cat B C) X))) (@one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)) (@id
  (Functor_cat A C) (@comp_cat_fapp0 A B C X U))) (@one_cat_product_pair_reindex_path A B C C1 Prod BP U X X X
  (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)) (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0
  (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma
  (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U))))
  (@one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@fapp0 (@Transf_cat B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B C) X)) (@fapp0 (@Transf_cat
  B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U
  X X) (@id (Functor_cat B C) X))) (@one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)) (@fapp0
  (@Transf_cat B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U))
  (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B C) X))) (@one_cat_product_family_pair A C C1 Prod BP
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C)
  (@comp_cat_fapp0 A B C X U)) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U))) (@eq_ap (@Transf A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)) (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0
  (Functor_cat A (Product_cat C C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma
  (Functor A C) (λ _ : τ (Functor A C), Functor A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)))) (λ h :
  τ (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)), @one_cat_product_family_pair A C C1 Prod BP
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) h (@fapp0 (@Transf_cat B C X X)
  (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U X X)
  (@id (Functor_cat B C) X))) (@fapp0 (@Transf_cat B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U)) (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B C) X)) (@id (Functor_cat A
  C) (@comp_cat_fapp0 A B C X U)) (@prewhisker_identity_path A B C U X)) (@eq_ap (@Transf A C (@comp_cat_fapp0 A
  B C X U) (@comp_cat_fapp0 A B C X U)) (@Transf A C (@comp_cat_fapp0 A B C X U) (@fapp0 (Functor_cat A (Product_cat C
  C)) (Functor_cat A C) (@comp_cat_cov_func A (Product_cat C C) C Prod) (@Struct_sigma (Functor A C) (λ _ : τ (Functor
  A C), Functor A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U)))) (λ h : τ (@Transf A C (@comp_cat_fapp0
  A B C X U) (@comp_cat_fapp0 A B C X U)), @one_cat_product_family_pair A C C1 Prod BP (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)) h)
  (@fapp0 (@Transf_cat B C X X) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U))
  (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B C) X)) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X
  U)) (@prewhisker_identity_path A B C U X))));

// Restriction preserves the actual whole addition operation, with original product choices.
symbol one_cat_additive_family_reindex_path [A B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (U : τ (Functor A B)) (X Y : τ (Functor B C))
  (f g : τ (@Transf B C X Y))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func
  A B C U X Y) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y f g)) (@one_cat_additive_family_add A C C1 Prod t
  V T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)))
≔ (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B C U X Y) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y f g)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B C U X Y) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t V T0
  X X Y f g) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat
  B C) X) (@id (Functor_cat B C) X)))) (@one_cat_additive_family_add A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A
  C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) g)) (@eq_ap
  (@Transf B C X Y) (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (λ h : τ (@Transf B C X Y),
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X Y) h)) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y f g)
  (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t V T0 X X Y f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X))) (@one_cat_additive_family_add_formula_path B C C1 Prod t V T0 X Y f g)) (@eq_trans
  (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U
  X Y) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t V T0 X X Y f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X)))) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))
  U) (@comp_cat_fapp0 A B C Y U) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y) (@one_cat_copair_family B C C1 Prod
  t V T0 X X Y f g)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X (@comp_cat_fapp0 B (Product_cat C C) C Prod
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))))
  (@one_cat_additive_family_add A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) g)) (@prewhisker_comp_path A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))
  Y (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X)) (@one_cat_copair_family B C C1 Prod t V T0 X X Y f g)) (@eq_trans (@Transf A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) U) (@comp_cat_fapp0 A B C Y U) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U (@comp_cat_fapp0
  B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y)
  (@one_cat_copair_family B C C1 Prod t V T0 X X Y f g)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X)))) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))
  U) (@comp_cat_fapp0 A B C Y U) (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X)))) (@one_cat_additive_family_add A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A
  C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) g)) (@eq_ap
  (@Transf A C (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ :
  τ (Functor B C), Functor B C) X X)) U) (@comp_cat_fapp0 A B C Y U)) (@Transf A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (λ h : τ (@Transf A C (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C
  Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) U) (@comp_cat_fapp0 A B C Y U)),
  (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C
  C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) U) (@comp_cat_fapp0 A B C Y U) h
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B C U (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X X)) Y) (@one_cat_copair_family B C C1 Prod t V T0 X X Y f g)) (@one_cat_copair_family
  A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) g)) (@one_cat_copair_reindex_path A B C C1
  Prod t V T0 U X X Y f g)) (@eq_trans (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C
  C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) U) (@comp_cat_fapp0 A B C Y U)
  (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0
  A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) g)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C
  U X (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X))) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C)
  X) (@id (Functor_cat B C) X)))) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))
  U) (@comp_cat_fapp0 A B C Y U) (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)) (@one_cat_product_family_pair A C C1 Prod (@additive_binary_products C
  Prod t V) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C)
  (@comp_cat_fapp0 A B C X U)) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)))) (@one_cat_additive_family_add A C
  C1 Prod t V T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A
  C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)) (@eq_ap (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C
  (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))
  U)) (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (λ h : τ (@Transf A C (@comp_cat_fapp0 A B
  C X U) (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X X)) U)), (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A
  B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) U) (@comp_cat_fapp0 A B C Y U) (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)) h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X (@comp_cat_fapp0 B
  (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t V) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X))) (@one_cat_product_family_pair A C C1 Prod (@additive_binary_products C Prod t V)
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C)
  (@comp_cat_fapp0 A B C X U)) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)))
  (@one_cat_product_diagonal_reindex_path A B C C1 Prod (@additive_binary_products C Prod t V) U X)) (@eq_sym
  (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@one_cat_additive_family_add A C C1 Prod t V
  T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)) (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) U) (@comp_cat_fapp0 A B C Y U) (@one_cat_copair_family A C C1 Prod t V T0 (@comp_cat_fapp0 A
  B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0
  (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) g)) (@one_cat_product_family_pair A C C1 Prod (@additive_binary_products C
  Prod t V) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U) (@id (Functor_cat A C)
  (@comp_cat_fapp0 A B C X U)) (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U))))
  (@one_cat_additive_family_add_formula_path A C C1 Prod t V T0 (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y
  U) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U X Y) f) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat A C (@comp_cat_fapp0 A B C X U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U X Y) g)))))));
