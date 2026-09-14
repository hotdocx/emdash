require open emdash.emdash3_2_one_cat_shear_additive_inverse_paths;
require open emdash.emdash3_2_one_cat_biproduct_family_reindex;
require open emdash.emdash3_2_one_cat_negative_families;
require open emdash.emdash3_2_one_cat_kernel_pullback_lifts;
require open emdash.emdash3_2_one_cat_difference_families;

/* Whole additive inverse laws for the original restricted negative identity. */

// Restrict the original universal law; no new negative identity is selected.
symbol one_cat_negative_family_add_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C))
  : τ (@= (@Transf B C X X) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id (Functor_cat B C) X)
  (@one_cat_negative_family_transf B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X))
≔ (@eq_trans (@Transf B C X X) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id (Functor_cat B C) X)
  (@one_cat_negative_family_transf B C C1 Prod t A T0 X)) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@fapp0
  (@Transf_cat C C (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C)
  (@id_func C)) (@id (Functor_cat C C) (@id_func C))) (@fapp0 (@Transf_cat C C (@id_func C) (@id_func C)) (@Transf_cat
  B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) (@one_cat_negative_identity_transf C C1 Prod t
  A T0))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X) (@eq_ap (@Transf B C X
  X) (@Transf B C X X) (λ h : τ (@Transf B C X X), (@one_cat_additive_family_add B C C1 Prod t A T0 X X h
  (@one_cat_negative_family_transf B C C1 Prod t A T0 X))) (@id (Functor_cat B C) X) (@fapp0 (@Transf_cat C C
  (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) (@id
  (Functor_cat C C) (@id_func C))) (@eq_sym (@Transf B C X X) (@fapp0 (@Transf_cat C C (@id_func C) (@id_func C))
  (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) (@id (Functor_cat C C) (@id_func
  C))) (@id (Functor_cat B C) X) (@prewhisker_identity_path B C C X (@id_func C)))) (@eq_trans (@Transf B C X X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@fapp0 (@Transf_cat C C (@id_func C) (@id_func C))
  (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) (@id (Functor_cat C C) (@id_func
  C))) (@fapp0 (@Transf_cat C C (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X
  (@id_func C) (@id_func C)) (@one_cat_negative_identity_transf C C1 Prod t A T0))) (@fapp0 (@Transf_cat C C (@id_func
  C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C))
  (@one_cat_additive_family_add C C C1 Prod t A T0 (@id_func C) (@id_func C) (@id (Functor_cat C C) (@id_func C))
  (@one_cat_negative_identity_transf C C1 Prod t A T0))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X) (@eq_sym (@Transf B C X X) (@fapp0 (@Transf_cat C C (@id_func C)
  (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C))
  (@one_cat_additive_family_add C C C1 Prod t A T0 (@id_func C) (@id_func C) (@id (Functor_cat C C) (@id_func C))
  (@one_cat_negative_identity_transf C C1 Prod t A T0))) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@fapp0
  (@Transf_cat C C (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C)
  (@id_func C)) (@id (Functor_cat C C) (@id_func C))) (@fapp0 (@Transf_cat C C (@id_func C) (@id_func C)) (@Transf_cat
  B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) (@one_cat_negative_identity_transf C C1 Prod t
  A T0))) (@one_cat_additive_family_reindex_path B C C C1 Prod t A T0 X (@id_func C) (@id_func C) (@id
  (Functor_cat C C) (@id_func C)) (@one_cat_negative_identity_transf C C1 Prod t A T0))) (@eq_trans (@Transf B C X X)
  (@fapp0 (@Transf_cat C C (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X
  (@id_func C) (@id_func C)) (@one_cat_additive_family_add C C C1 Prod t A T0 (@id_func C) (@id_func C) (@id
  (Functor_cat C C) (@id_func C)) (@one_cat_negative_identity_transf C C1 Prod t A T0))) (@fapp0 (@Transf_cat C C
  (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C))
  (@zero_arrow_family_zero_transf C C t (@additive_terminal_object C Prod t A) T0 (@id_func C) (@id_func C)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X) (@eq_ap (@Transf C C (@id_func
  C) (@id_func C)) (@Transf B C X X) (λ h : τ (@Transf C C (@id_func C) (@id_func C)), (@fapp0 (@Transf_cat C C
  (@id_func C) (@id_func C)) (@Transf_cat B C X X) (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) h))
  (@one_cat_additive_family_add C C C1 Prod t A T0 (@id_func C) (@id_func C) (@id (Functor_cat C C) (@id_func C))
  (@one_cat_negative_identity_transf C C1 Prod t A T0)) (@zero_arrow_family_zero_transf C C t
  (@additive_terminal_object C Prod t A) T0 (@id_func C) (@id_func C)) (@one_cat_negative_identity_add_path C C1
  Prod t A T0)) (@one_cat_zero_family_prewhisker_path B C C C1 t (@additive_terminal_object C Prod t A) T0 X (@id_func
  C) (@id_func C)))));

// f+(−f)=0 follows by whole bilinearity and the original zero factorization.
symbol one_cat_additive_family_inverse_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1
  Prod t A T0 X Y f)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y))
≔ (@eq_trans (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1
  Prod t A T0 X Y f)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@comp_fapp0 (Functor_cat B C) X Y Y
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y) (@eq_ap (@Transf B C X Y) (@Transf B C X Y) (λ h : τ (@Transf B C X
  Y), (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f h)) (@one_cat_negative_family B C C1 Prod t A T0 X Y f)
  (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)
  (@one_cat_negative_family_formula_path B C C1 Prod t A T0 X Y f)) (@eq_trans (@Transf B C X Y)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@comp_fapp0 (Functor_cat B C) X Y Y
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)) (@comp_fapp0 (Functor_cat B C) X Y Y
  (@one_cat_additive_family_add B C C1 Prod t A T0 Y Y (@id (Functor_cat B C) Y) (@one_cat_negative_family_transf B C
  C1 Prod t A T0 Y)) f) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y) (@eq_sym
  (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_additive_family_add B C C1 Prod t A T0 Y Y (@id
  (Functor_cat B C) Y) (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) f) (@one_cat_additive_family_add B C C1
  Prod t A T0 X Y f (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f))
  (@one_cat_additive_family_precompose_path B C C1 Prod t A T0 X Y Y (@id (Functor_cat B C) Y)
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)) (@eq_trans (@Transf B C X Y) (@comp_fapp0 (Functor_cat B
  C) X Y Y (@one_cat_additive_family_add B C C1 Prod t A T0 Y Y (@id (Functor_cat B C) Y)
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) f) (@comp_fapp0 (Functor_cat B C) X Y Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Y) f)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y) (@eq_ap (@Transf B C Y Y)
  (@Transf B C X Y) (λ h : τ (@Transf B C Y Y), (@comp_fapp0 (Functor_cat B C) X Y Y h f))
  (@one_cat_additive_family_add B C C1 Prod t A T0 Y Y (@id (Functor_cat B C) Y) (@one_cat_negative_family_transf B C
  C1 Prod t A T0 Y)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Y)
  (@one_cat_negative_family_add_path B C C1 Prod t A T0 Y)) (@one_cat_zero_family_precompose_path B C C1 t
  (@additive_terminal_object C Prod t A) T0 X Y Y f))));

// The existing whole difference operation has the same self-zero law.
symbol one_cat_difference_family_self_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f f) (@zero_arrow_family_zero_transf B
  C t (@additive_terminal_object C Prod t A) T0 X Y))
≔ @eq_trans (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f f) (@one_cat_additive_family_add B
  C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X Y f)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)
    (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f f)
    (@one_cat_additive_family_inverse_path B C C1 Prod t A T0 X Y f);
