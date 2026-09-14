/* Whole subtraction f−g through the original native addition and derived negation. */
require open emdash.emdash3_2_one_cat_negative_families;

// The signed input map and addition are both internal functors.
symbol one_cat_difference_family_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C))
  : τ (Functor (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y))
≔ @comp_cat_fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (Hom_cat (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)) (@Transf_cat B C X Y)
  (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) (@Product_map_func (@Transf_cat B C X Y) (@Transf_cat B C
  X Y) (@Transf_cat B C X Y) (@Transf_cat B C X Y) (@id_func (@Transf_cat B C X Y))
  (@one_cat_negative_family_func B C C1 Prod t A T0 X Y));

// Subtraction applies that whole functor to the original pair f/g.
symbol one_cat_difference_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y))
  : τ (@Transf B C X Y)
≔ @fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y)
  (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) (@Struct_sigma (@Transf B C X Y) (λ _ : τ (@Transf B
  C X Y), @Transf B C X Y) f g);

// The native operation agrees with the already constructed addition/negation.
symbol one_cat_difference_family_formula_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f g)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X Y g)))
≔ @eq_refl (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B
  C C1 Prod t A T0 X Y g));

// Original scalar subtraction is a derived component observation.
symbol one_cat_difference_family_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_difference_family B C C1
  Prod t A T0 X Y f g)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y
  b) (@tapp0_fapp0 B C X Y b g))))
≔ (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_difference_family B C
  C1 Prod t A T0 X Y f g)) (@tapp0_fapp0 B C X Y b (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g))) (@preadditive_hom_add C (@additive_preadditive C Prod t
  A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@preadditive_hom_neg C (@additive_preadditive C
  Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b g))) (@eq_ap (@Transf B C X Y) (Hom C (@fapp0 B
  C X b) (@fapp0 B C Y b)) (λ h : τ (@Transf B C X Y), @tapp0_fapp0 B C X Y b h) (@one_cat_difference_family B C
  C1 Prod t A T0 X Y f g) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C
  C1 Prod t A T0 X Y g)) (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f g)) (@eq_trans (Hom C
  (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g))) (@preadditive_hom_add C (@additive_preadditive C Prod t
  A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g))) (@preadditive_hom_add C (@additive_preadditive C Prod t
  A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@preadditive_hom_neg C (@additive_preadditive C
  Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b g)))
  (@one_cat_additive_family_add_component_path B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t
  A T0 X Y g) b) (@eq_ap (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (λ h : τ
  (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)), (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X
  b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) h)) (@tapp0_fapp0 B C X Y b (@one_cat_negative_family B C C1
  Prod t A T0 X Y g)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b g)) (@one_cat_negative_family_component_neg_path B C C1 Prod t A T0 X Y g b))));
