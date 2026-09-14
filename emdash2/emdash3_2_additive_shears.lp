/* Scalar inverses certify an already constructed whole shear. */
require open emdash.emdash3_2_computational_weak_pullback_compatibility;

// Cancel opposite summands without changing the original group structure.
symbol abelian_group_positive_inverse_sum_path [G : Grpd] (S : τ (@AbelianGroupStructure G)) (a b : τ G)
  : τ (@= G (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) b)) b)
≔ (@eq_trans G (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) b))
  (@abelian_group_ops_add G (@abelian_group_structure_ops G S) (@abelian_group_ops_add G (@abelian_group_structure_ops
  G S) a (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a)) b) b (@eq_sym G (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a)) b) (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) a (@abelian_group_ops_add G (@abelian_group_structure_ops G S)
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) b)) ((@abelian_group_add_assoc_law G S) a
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) b)) (@eq_trans G (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a)) b) (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_zero G (@abelian_group_structure_ops G S)) b) b (@eq_ap G G
  (λ z : τ G, (@abelian_group_ops_add G (@abelian_group_structure_ops G S) z b)) (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) a (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a))
  (@abelian_group_ops_zero G (@abelian_group_structure_ops G S)) ((@abelian_group_add_inv_law G S) a))
  (@abelian_group_add_zero_left_path G S b)));

// Cancel opposite summands without changing the original group structure.
symbol abelian_group_negative_inverse_sum_path [G : Grpd] (S : τ (@AbelianGroupStructure G)) (a b : τ G)
  : τ (@= G (@abelian_group_ops_add G (@abelian_group_structure_ops G S) (@abelian_group_ops_neg G
  (@abelian_group_structure_ops G S) a) (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a b)) b)
≔ (@eq_trans G (@abelian_group_ops_add G (@abelian_group_structure_ops G S) (@abelian_group_ops_neg G
  (@abelian_group_structure_ops G S) a) (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a b))
  (@abelian_group_ops_add G (@abelian_group_structure_ops G S) (@abelian_group_ops_add G (@abelian_group_structure_ops
  G S) (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) a) b) b (@eq_sym G (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_add G (@abelian_group_structure_ops G S)
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) a) b) (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a)
  (@abelian_group_ops_add G (@abelian_group_structure_ops G S) a b)) ((@abelian_group_add_assoc_law G S)
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) a b)) (@eq_trans G (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_add G (@abelian_group_structure_ops G S)
  (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) a) b) (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_zero G (@abelian_group_structure_ops G S)) b) b (@eq_ap G G
  (λ z : τ G, (@abelian_group_ops_add G (@abelian_group_structure_ops G S) z b)) (@abelian_group_ops_add G
  (@abelian_group_structure_ops G S) (@abelian_group_ops_neg G (@abelian_group_structure_ops G S) a) a)
  (@abelian_group_ops_zero G (@abelian_group_structure_ops G S)) (@abelian_group_add_inv_left_path G S a))
  (@abelian_group_add_zero_left_path G S b)));

// S(x,y)=(x,x+y), written through the original product and addition.
symbol additive_shear [C : Cat] [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ
  (@AdditiveCategory C Prod t)) (X : τ (Obj C)) : τ (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)))
≔ (@binary_products_pair_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) X X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)
  (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)));

// The scalar inverse uses the original Hom negation.
symbol additive_shear_inverse [C : Cat] [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ
  (@AdditiveCategory C Prod t)) (X : τ (Obj C)) : τ (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)))
≔ (@binary_products_pair_fapp0 C Prod (@additive_binary_products C Prod t A) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) X X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)
  (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X
  X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X))
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X)));

// The left inverse follows from product β/η and original additive cancellation.
symbol additive_shear_left_path [C : Cat] [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ
  (@AdditiveCategory C Prod t)) (X : τ (Obj C))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  (@additive_shear_inverse C Prod t A X) (@additive_shear C Prod t A X)) (@id C (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C X X))))
≔ (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  (@additive_shear_inverse C Prod t A X) (@additive_shear C Prod t A X)) (@binary_products_pair_fapp0 C
  Prod (@additive_binary_products C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)) (@id C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)))
  (@additive_pair_congr_path C Prod t A (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj1_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X) _ (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C
  Prod t A) X X) (@eq_refl (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X)
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@eq_trans (Hom C (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair
  C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_add C (@additive_preadditive
  C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)) (@additive_shear C Prod t A X)) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@comp_fapp0 C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X
  X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@additive_shear C
  Prod t A X)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X))) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X) ((@preadditive_comp_add_left_law C (@additive_preadditive C Prod t
  A)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X
  X)) X (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  X X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X))
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@additive_shear C Prod t A
  X)) (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@comp_fapp0 C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X
  X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@additive_shear C
  Prod t A X)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X))) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_neg
  C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X))) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C
  Prod t A) X X) (@additive_add_congr_path C Prod t A (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) X (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X))
  (@additive_shear C Prod t A X)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products
  C Prod t A) X X)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)) (@preadditive_comp_neg_left_path C (@additive_preadditive C Prod t
  A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X
  X)) X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@additive_shear C Prod
  t A X)) (@eq_refl (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)))) (@abelian_group_negative_inverse_sum_path (Hom C (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@preadditive_hom_structure C (@additive_preadditive C Prod t
  A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t
  A) X X))))) (@binary_products_pair_eta_path C Prod (@additive_binary_products C Prod t A) X X));

// The right inverse follows from product β/η and original additive cancellation.
symbol additive_shear_right_path [C : Cat] [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ
  (@AdditiveCategory C Prod t)) (X : τ (Obj C))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  (@additive_shear C Prod t A X) (@additive_shear_inverse C Prod t A X)) (@id C (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C X X))))
≔ (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  (@additive_shear C Prod t A X) (@additive_shear_inverse C Prod t A X)) (@binary_products_pair_fapp0 C
  Prod (@additive_binary_products C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)) (@id C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)))
  (@additive_pair_congr_path C Prod t A (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj1_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X) _ (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C
  Prod t A) X X) (@eq_refl (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X)
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@eq_trans (Hom C (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair
  C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_add C (@additive_preadditive
  C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t
  A) X X)) (@additive_shear_inverse C Prod t A X)) (@preadditive_hom_add C (@additive_preadditive C Prod t A)
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_neg C (@additive_preadditive C Prod t A)
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X)) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod
  t A) X X))) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X)
  ((@preadditive_comp_add_left_law C (@additive_preadditive C Prod t A)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C
  Prod t A) X X) (@additive_shear_inverse C Prod t A X)) (@abelian_group_positive_inverse_sum_path (Hom C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@preadditive_hom_structure C (@additive_preadditive C
  Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X) (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t
  A) X X)))) (@binary_products_pair_eta_path C Prod (@additive_binary_products C Prod t A) X X));

// Fixed-forward equivalence retains the concrete scalar inverse in both slots.
symbol additive_shear_omega_along [C : Cat] [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ
  (@AdditiveCategory C Prod t)) (X : τ (Obj C))
  : τ (@OmegaEquivAlong C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) (@additive_shear C Prod t A X))
≔ @omega_equiv_along_intro C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C
  Prod (@Product_pair C C X X)) (@additive_shear C Prod t A X) (@additive_shear_inverse C Prod t A X)
  (@additive_shear_inverse C Prod t A X)
    (@additive_shear_left_path C Prod t A X) (@additive_shear_right_path C Prod t A X);

// Scalar readback uses the original additive inverse and product β.
symbol additive_shear_inverse_negative_projection_path
  [C : Cat] [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (X : τ (Obj
  C))
  : τ (@= (Hom C X X) (@comp_fapp0 C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@comp_fapp0 C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@additive_shear_inverse C
  Prod t A X)) (@additive_inj1_fapp0 C Prod t A X X)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) X X
  (@id C X)))
≔ (@eq_trans (Hom C X X) (@comp_fapp0 C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@comp_fapp0 C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@additive_shear_inverse C
  Prod t A X)) (@additive_inj1_fapp0 C Prod t A X X)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) X X
  (@comp_fapp0 C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@additive_inj1_fapp0 C Prod t A X
  X)) (@preadditive_hom_zero C (@additive_preadditive C Prod t A) X X)) (@preadditive_hom_neg C (@additive_preadditive
  C Prod t A) X X (@id C X)) ((@preadditive_comp_add_left_law C (@additive_preadditive C Prod t A)) X (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C X X)) X (@preadditive_hom_neg C (@additive_preadditive C Prod t A)
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X)) (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod
  t A) X X) (@additive_inj1_fapp0 C Prod t A X X)) (@eq_trans (Hom C X X) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) X X (@comp_fapp0 C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X
  (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X))
  X (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X)) (@additive_inj1_fapp0 C Prod t A
  X X)) (@preadditive_hom_zero C (@additive_preadditive C Prod t A) X X)) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) X X (@preadditive_hom_neg C (@additive_preadditive C Prod t A) X X (@id C X))
  (@preadditive_hom_zero C (@additive_preadditive C Prod t A) X X)) (@preadditive_hom_neg C (@additive_preadditive C
  Prod t A) X X (@id C X)) (@additive_add_congr_path C Prod t A X X _ (@preadditive_hom_neg C (@additive_preadditive C
  Prod t A) X X (@id C X)) (@preadditive_hom_zero C (@additive_preadditive C Prod t A) X X) (@preadditive_hom_zero C
  (@additive_preadditive C Prod t A) X X) (@preadditive_comp_neg_left_path C (@additive_preadditive C Prod t A) X
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X (@binary_products_proj1_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X) (@additive_inj1_fapp0 C Prod t A X X)) (@eq_refl (Hom C X X)
  (@preadditive_hom_zero C (@additive_preadditive C Prod t A) X X))) ((@abelian_group_add_zero_law (Hom C X X)
  (@preadditive_hom_structure C (@additive_preadditive C Prod t A) X X)) (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) X X (@id C X)))));
