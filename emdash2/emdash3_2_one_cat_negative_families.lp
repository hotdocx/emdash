/* Native whole negation by generic restriction and postcomposition of −id. */
require open emdash.emdash3_2_one_cat_negative_identity;
require open emdash.emdash3_2_one_cat_family_naturality_paths;

// Restrict the one universal negative identity to the original family X.
symbol one_cat_negative_family_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C)) : τ (@Transf B C X X)
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B C C X (@id_func C) (@id_func C)) (@one_cat_negative_identity_transf C
  C1 Prod t A T0);

// The whole family action recovers the original scalar −id.
symbol one_cat_negative_family_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) (@tapp0_fapp0 B C X X b (@one_cat_negative_family_transf B C
  C1 Prod t A T0 X)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b) (@id
  C (@fapp0 B C X b))))
≔ @eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C X b)) _ _ _
    (@prewhisker_component_path B C C X (@id_func C) (@id_func C) (@one_cat_negative_identity_transf C C1 Prod t
  A T0) b)
    (@one_cat_negative_identity_component_path C C1 Prod t A T0 (@fapp0 B C X b));

// Negation is an actual native Hom functor, with its inherited higher action.
symbol one_cat_negative_family_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C))
  : τ (Functor (@Transf_cat B C X Y) (@Transf_cat B C X Y))
≔ @hom_postcomp_func (Functor_cat B C) (Functor_cat B C) (@id_func (Functor_cat B C)) X Y Y
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y);

// Apply the native functor to a whole f.
symbol one_cat_negative_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
  : τ (@Transf B C X Y)
≔ @fapp0 (@Transf_cat B C X Y) (@Transf_cat B C X Y) (@one_cat_negative_family_func B C C1 Prod t A T0 X Y) f;

// The composition formula is a derived view; runtime keeps postcomposition as owner.
symbol one_cat_negative_family_formula_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y f) (@comp_fapp0 (Functor_cat B C) X
  Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f))
≔ @eq_refl (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t
  A T0 Y) f);

// Original component negation is a downstream observation of the whole map.
symbol one_cat_negative_family_component_neg_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_negative_family B C C1
  Prod t A T0 X Y f)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f)))
≔ (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_negative_family B C C1
  Prod t A T0 X Y f)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Y b) (@tapp0_fapp0 B C Y Y b
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) (@tapp0_fapp0 B C X Y b f)) (@preadditive_hom_neg C
  (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f)) (@eq_ap (@Transf B
  C X Y) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (λ h : τ (@Transf B C X Y), @tapp0_fapp0 B C X Y b h)
  (@one_cat_negative_family B C C1 Prod t A T0 X Y f) (@comp_fapp0 (Functor_cat B C) X Y Y
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f) (@one_cat_negative_family_formula_path B C C1
  Prod t A T0 X Y f)) (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 B C
  Y b) (@fapp0 B C Y b) (@tapp0_fapp0 B C Y Y b (@one_cat_negative_family_transf B C C1 Prod t A T0 Y))
  (@tapp0_fapp0 B C X Y b f)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Y b) (@preadditive_hom_neg
  C (@additive_preadditive C Prod t A) (@fapp0 B C Y b) (@fapp0 B C Y b) (@id C (@fapp0 B C Y b))) (@tapp0_fapp0 B C X
  Y b f)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B
  C X Y b f)) (@eq_ap (Hom C (@fapp0 B C Y b) (@fapp0 B C Y b)) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (λ h : τ
  (Hom C (@fapp0 B C Y b) (@fapp0 B C Y b)), (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Y b) h
  (@tapp0_fapp0 B C X Y b f))) (@tapp0_fapp0 B C Y Y b (@one_cat_negative_family_transf B C C1 Prod t A T0 Y))
  (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C Y b) (@fapp0 B C Y b) (@id C (@fapp0 B C Y
  b))) (@one_cat_negative_family_component_path B C C1 Prod t A T0 Y b)) (@preadditive_comp_neg_left_path C
  (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Y b) (@id C (@fapp0 B C Y b))
  (@tapp0_fapp0 B C X Y b f))));

// Naturality is inherited from the one universal whole negative identity.
symbol one_cat_negative_family_centrality_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X X Y f (@one_cat_negative_family_transf B C C1 Prod
  t A T0 X)) (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f))
≔ @one_cat_family_naturality_path B C C C1 (@id_func C) (@id_func C) (@one_cat_negative_identity_transf C C1
  Prod t A T0) X Y f;

// −(g∘f)=(−g)∘f by whole associativity and the native composition view.
symbol one_cat_negative_family_precompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y Z : τ (Functor B C))
  (f : τ (@Transf B C X Y)) (g : τ (@Transf B C Y Z))
  : τ (@= (@Transf B C X Z) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y
  Z g f)) (@comp_fapp0 (Functor_cat B C) X Y Z (@one_cat_negative_family B C C1 Prod t A T0 Y Z g) f))
≔ (@eq_trans (@Transf B C X Z) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X
  Y Z g f)) (@comp_fapp0 (Functor_cat B C) X Z Z (@one_cat_negative_family_transf B C C1 Prod t A T0 Z)
  (@comp_fapp0 (Functor_cat B C) X Y Z g f)) (@comp_fapp0 (Functor_cat B C) X Y Z (@one_cat_negative_family B C
  C1 Prod t A T0 Y Z g) f) (@one_cat_negative_family_formula_path B C C1 Prod t A T0 X Z (@comp_fapp0
  (Functor_cat B C) X Y Z g f)) (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Z Z
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) (@comp_fapp0 (Functor_cat B C) X Y Z g f)) (@comp_fapp0
  (Functor_cat B C) X Y Z (@comp_fapp0 (Functor_cat B C) Y Z Z (@one_cat_negative_family_transf B C C1 Prod t A
  T0 Z) g) f) (@comp_fapp0 (Functor_cat B C) X Y Z (@one_cat_negative_family B C C1 Prod t A T0 Y Z g) f)
  (@comp_assoc (Functor_cat B C) X Y Z Z (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) g f) (@eq_ap
  (@Transf B C Y Z) (@Transf B C X Z) (λ h : τ (@Transf B C Y Z), (@comp_fapp0 (Functor_cat B C) X Y Z h f))
  (@comp_fapp0 (Functor_cat B C) Y Z Z (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) g)
  (@one_cat_negative_family B C C1 Prod t A T0 Y Z g) (@eq_sym (@Transf B C Y Z) (@one_cat_negative_family
  B C C1 Prod t A T0 Y Z g) (@comp_fapp0 (Functor_cat B C) Y Z Z (@one_cat_negative_family_transf B C C1 Prod t
  A T0 Z) g) (@one_cat_negative_family_formula_path B C C1 Prod t A T0 Y Z g)))));

// −(g∘f)=g∘(−f) follows from the same whole naturality.
symbol one_cat_negative_family_postcompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y Z : τ (Functor B C))
  (f : τ (@Transf B C X Y)) (g : τ (@Transf B C Y Z))
  : τ (@= (@Transf B C X Z) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y
  Z g f)) (@comp_fapp0 (Functor_cat B C) X Y Z g (@one_cat_negative_family B C C1 Prod t A T0 X Y f)))
≔ (@eq_trans (@Transf B C X Z) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X
  Y Z g f)) (@comp_fapp0 (Functor_cat B C) X Z Z (@one_cat_negative_family_transf B C C1 Prod t A T0 Z)
  (@comp_fapp0 (Functor_cat B C) X Y Z g f)) (@comp_fapp0 (Functor_cat B C) X Y Z g (@one_cat_negative_family B
  C C1 Prod t A T0 X Y f)) (@one_cat_negative_family_formula_path B C C1 Prod t A T0 X Z (@comp_fapp0
  (Functor_cat B C) X Y Z g f)) (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Z Z
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) (@comp_fapp0 (Functor_cat B C) X Y Z g f)) (@comp_fapp0
  (Functor_cat B C) X Y Z (@comp_fapp0 (Functor_cat B C) Y Z Z (@one_cat_negative_family_transf B C C1 Prod t A
  T0 Z) g) f) (@comp_fapp0 (Functor_cat B C) X Y Z g (@one_cat_negative_family B C C1 Prod t A T0 X Y f))
  (@comp_assoc (Functor_cat B C) X Y Z Z (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) g f) (@eq_trans
  (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z (@comp_fapp0 (Functor_cat B C) Y Z Z
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) g) f) (@comp_fapp0 (Functor_cat B C) X Y Z (@comp_fapp0
  (Functor_cat B C) Y Y Z g (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) f) (@comp_fapp0 (Functor_cat
  B C) X Y Z g (@one_cat_negative_family B C C1 Prod t A T0 X Y f)) (@eq_ap (@Transf B C Y Z) (@Transf B C X Z)
  (λ h : τ (@Transf B C Y Z), (@comp_fapp0 (Functor_cat B C) X Y Z h f)) (@comp_fapp0 (Functor_cat B C) Y Z Z
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) g) (@comp_fapp0 (Functor_cat B C) Y Y Z g
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) (@eq_sym (@Transf B C Y Z) (@comp_fapp0 (Functor_cat B
  C) Y Y Z g (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) (@comp_fapp0 (Functor_cat B C) Y Z Z
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Z) g) (@one_cat_negative_family_centrality_path B C
  C1 Prod t A T0 Y Z g))) (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z (@comp_fapp0 (Functor_cat
  B C) Y Y Z g (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) f) (@comp_fapp0 (Functor_cat B C) X Y Z g
  (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)) (@comp_fapp0
  (Functor_cat B C) X Y Z g (@one_cat_negative_family B C C1 Prod t A T0 X Y f)) (@eq_sym (@Transf B C X Z)
  (@comp_fapp0 (Functor_cat B C) X Y Z g (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B
  C C1 Prod t A T0 Y) f)) (@comp_fapp0 (Functor_cat B C) X Y Z (@comp_fapp0 (Functor_cat B C) Y Y Z g
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y)) f) (@comp_assoc (Functor_cat B C) X Y Y Z g
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)) (@eq_ap (@Transf B C X Y) (@Transf B C X Z) (λ h :
  τ (@Transf B C X Y), (@comp_fapp0 (Functor_cat B C) X Y Z g h)) (@comp_fapp0 (Functor_cat B C) X Y Y
  (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f) (@one_cat_negative_family B C C1 Prod t A T0 X
  Y f) (@eq_sym (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y f) (@comp_fapp0 (Functor_cat
  B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f)
  (@one_cat_negative_family_formula_path B C C1 Prod t A T0 X Y f)))))));
