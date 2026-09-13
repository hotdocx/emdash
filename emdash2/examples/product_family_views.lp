/* Projection views, retained normal forms and guarded component observations. */
require open emdash.emdash3_2_product_family_views;

assert [B C : Cat] (F : τ (Functor B C))
  ⊢ @eq_refl (Functor B C) F
    : τ (@= (Functor B C)
        (sigma_Fst (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) F)) F);
assert [B C : Cat] (F : τ (Functor B C))
  ⊢ @eq_refl (Functor B C) F
    : τ (@= (Functor B C)
        (sigma_Snd (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) F)) F);

assert [B C : Cat] (F : τ (Functor B C))
  ⊢ @eq_refl (Functor B C) F
    : τ (@= (Functor B C)
      (sigma_Fst (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) F)) F);

assert [B C : Cat] (F : τ (Functor B C))
  ⊢ @eq_refl (Functor B C) F
    : τ (@= (Functor B C)
      (sigma_Snd (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) F)) F);

// Existing raw associativity must remain usable when the functor is a composite.
assert [A B C : Cat] (F : τ (Functor A B)) (G : τ (Functor B C))
  ⊢ @eq_refl (Functor A C) (@comp_cat_fapp0 A B C G F)
    : τ (@= (Functor A C)
      (sigma_Fst (@comp_cat_fapp0 A C (Product_cat C C) (@product_diagonal_func C)
        (@comp_cat_fapp0 A B C G F))) (@comp_cat_fapp0 A B C G F));

assert [A B C : Cat] (F : τ (Functor A B)) (G : τ (Functor B C))
  ⊢ @eq_refl (Functor A C) (@comp_cat_fapp0 A B C G F)
    : τ (@= (Functor A C)
      (sigma_Snd (@comp_cat_fapp0 A C (Product_cat C C) (@product_diagonal_func C)
        (@comp_cat_fapp0 A B C G F))) (@comp_cat_fapp0 A B C G F));

// Constant composition likewise retains its original normal form.
assert [A C : Cat] (c : τ (Obj C))
  ⊢ @eq_refl (Functor A C) (@Const_func A C c)
    : τ (@= (Functor A C)
      (sigma_Fst (@comp_cat_fapp0 A C (Product_cat C C) (@product_diagonal_func C) (@Const_func A C c)))
      (@Const_func A C c));

assert [A C : Cat] (c : τ (Obj C))
  ⊢ @eq_refl (Functor A C) (@Const_func A C c)
    : τ (@= (Functor A C)
      (sigma_Snd (@comp_cat_fapp0 A C (Product_cat C C) (@product_diagonal_func C) (@Const_func A C c)))
      (@Const_func A C c));

assertnot [B C : Cat] (F G : τ (Functor B C))
  ⊢ @eq_refl (Functor B C) F
    : τ (@= (Functor B C)
      (sigma_Fst (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) F)) G);

assertnot [B C : Cat] (F G : τ (Functor B C))
  ⊢ @eq_refl (Functor B C) F
    : τ (@= (Functor B C)
      (sigma_Snd (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) F)) G);

// Neither whole diagonal application is changed into a paired runtime owner.
assertnot [B C : Cat] (F : τ (Functor B C))
  ⊢ @comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) F
    ≡ @Product_pair (Functor_cat B C) (Functor_cat B C) F F;

assertnot [B C : Cat] (F : τ (Functor B C))
  ⊢ @fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) F
    ≡ @Product_pair (Functor_cat B C) (Functor_cat B C) F F;

// Changing either retained factor or selected constant coordinate is rejected.
assertnot [A B C : Cat] (F F0 : τ (Functor A B)) (G : τ (Functor B C))
  ⊢ @eq_refl (Functor A C) (@comp_cat_fapp0 A B C G F)
    : τ (@= (Functor A C)
      (sigma_Fst (@comp_cat_fapp0 A C (Product_cat C C) (@product_diagonal_func C)
        (@comp_cat_fapp0 A B C G F))) (@comp_cat_fapp0 A B C G F0));
assertnot [A C : Cat] (c c0 : τ (Obj C))
  ⊢ @eq_refl (Functor A C) (@Const_func A C c)
    : τ (@= (Functor A C)
      (sigma_Snd (@comp_cat_fapp0 A C (Product_cat C C) (@product_diagonal_func C) (@Const_func A C c)))
      (@Const_func A C c0));

// The component view agrees with both cells of the same whole pair.
assert [B C : Cat] (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (b : τ (Obj B))
  ⊢ @eq_refl (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B
    C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
    (@product_diagonal_func C) X) (@Product_pair (Functor_cat B C) (Functor_cat B C) F G) b (@Product_pair
    (@Transf_cat B C X F) (@Transf_cat B C X G) f g)) : τ (@= (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X
    b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C)
    (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) (@Product_pair (Functor_cat B C) (Functor_cat
    B C) F G) b (@Product_pair (@Transf_cat B C X F) (@Transf_cat B C X G) f g)) (@Product_pair (Hom_cat C (@fapp0 B C
    X b) (@fapp0 B C F b))
      (Hom_cat C (@fapp0 B C X b) (@fapp0 B C G b))
      (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g)));
assertnot [B C : Cat] (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (f0 : τ (@Transf B C X F)) (b : τ (Obj B))
  ⊢ @eq_refl (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B
    C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
    (@product_diagonal_func C) X) (@Product_pair (Functor_cat B C) (Functor_cat B C) F G) b (@Product_pair
    (@Transf_cat B C X F) (@Transf_cat B C X G) f g)) : τ (@= (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X
    b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C)
    (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) (@Product_pair (Functor_cat B C) (Functor_cat
    B C) F G) b (@Product_pair (@Transf_cat B C X F) (@Transf_cat B C X G) f g)) (@Product_pair (Hom_cat C (@fapp0 B C
    X b) (@fapp0 B C F b))
      (Hom_cat C (@fapp0 B C X b) (@fapp0 B C G b))
      (@tapp0_fapp0 B C X F b f0) (@tapp0_fapp0 B C X G b g)));
assertnot [B C : Cat] (X F G : τ (Functor B C))
  (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (g0 : τ (@Transf B C X G)) (b : τ (Obj B))
  ⊢ @eq_refl (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B
    C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
    (@product_diagonal_func C) X) (@Product_pair (Functor_cat B C) (Functor_cat B C) F G) b (@Product_pair
    (@Transf_cat B C X F) (@Transf_cat B C X G) f g)) : τ (@= (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X
    b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C)
    (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) (@Product_pair (Functor_cat B C) (Functor_cat
    B C) F G) b (@Product_pair (@Transf_cat B C X F) (@Transf_cat B C X G) f g)) (@Product_pair (Hom_cat C (@fapp0 B C
    X b) (@fapp0 B C F b))
      (Hom_cat C (@fapp0 B C X b) (@fapp0 B C G b))
      (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g0)));
