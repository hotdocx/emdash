/* Reviewer-facing generic additive-category derivation. */

require open emdash.emdash3_2_additive_categories;

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@PreadditiveCategory C))
  (K : τ (@CartesianCategory C P t)) ⊢
  @additive_category_intro C P t S K
  : τ (@AdditiveCategory C P t);

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@AdditiveCategory C P t))
  (X : τ (Obj C)) ⊢
  @additive_initial_hom_contr C P t A X
  : τ (IsContr (Hom C t X));

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C)) ⊢
  @additive_inj1_fapp0 C P t A X Y
  : τ (Hom C X
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)));

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (f : τ (Hom C X Z))
  (g : τ (Hom C Y Z)) ⊢
  @additive_copair_fapp0 C P t A X Y Z f g
  : τ (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z);

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (f : τ (Hom C X Z))
  (g : τ (Hom C Y Z)) ⊢
  @additive_copair_inj1_path C P t A X Y Z f g
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z
        (@additive_copair_fapp0 C P t A X Y Z f g)
        (@additive_inj1_fapp0 C P t A X Y))
      f);

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@AdditiveCategory C P t))
  (X Y : τ (Obj C)) ⊢
  @additive_biproduct_identity_path C P t A X Y
  : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)))
      (@additive_biproduct_identity_sum C P t A X Y)
      (@id C
        (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y))));

assert (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (h : τ (Hom C
    (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z)) ⊢
  @additive_copair_eta_path C P t A X Y Z h
  : τ (@= (Hom C
      (@fapp0 (Product_cat C C) C P (@Product_pair C C X Y)) Z)
      (@additive_copair_fapp0 C P t A X Y Z
        (@comp_fapp0 C X _ Z h (@additive_inj1_fapp0 C P t A X Y))
        (@comp_fapp0 C Y _ Z h (@additive_inj2_fapp0 C P t A X Y)))
      h);
