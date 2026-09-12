/* NON-LIBRARY proof-time comparisons required by the polarity-isolation
   beta. Constant heads keep their runtime identities and all parameters. */
require open emdash.emdash3_2;

symbol constant_family_view [K : Cat] (A : Cat)
  : τ (@= (Functor K Cat_cat) (@Const_catd K A) (@Const_func K Cat_cat A))
≔ @eq_refl (Functor K Cat_cat) (@Const_func K Cat_cat A);

symbol constant_postcomp_view [A B C : Cat]
  (F : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Functor A C)
      (@Hom_fapp0 Cat_cat A A B C (@id Cat_cat A) F (@Const_func A B b))
      (@Const_func A C (@fapp0 B C F b)))
≔ @eq_refl (Functor A C) (@Const_func A C (@fapp0 B C F b));

symbol constant_reindex_view [A B : Cat]
  (G : τ (Functor B A)) (C : Cat)
  : τ (@= (Functor B Cat_cat)
      (@Hom_fapp0 Cat_cat A B Cat_cat Cat_cat G (@id Cat_cat Cat_cat)
        (@Const_catd A C)) (@Const_catd B C))
≔ @eq_refl (Functor B Cat_cat) (@Const_catd B C);

// Proof-time usability is deliberately not a runtime fold.
assertnot [K : Cat] (A : Cat) ⊢
  @Const_catd K A ≡ @Const_func K Cat_cat A;
assertnot [A B C : Cat] (F : τ (Functor B C)) (b : τ (Obj B)) ⊢
  @Hom_fapp0 Cat_cat A A B C (@id Cat_cat A) F (@Const_func A B b)
  ≡ @Const_func A C (@fapp0 B C F b);
assertnot [A B : Cat] (G : τ (Functor B A)) (C : Cat) ⊢
  @Hom_fapp0 Cat_cat A B Cat_cat Cat_cat G (@id Cat_cat Cat_cat)
    (@Const_catd A C) ≡ @Const_catd B C;

// Each unifier must retain its category/object parameter constraints.
assertnot [K : Cat] (A B : Cat) ⊢
  @eq_refl (Functor K Cat_cat) (@Const_func K Cat_cat B)
  : τ (@= (Functor K Cat_cat) (@Const_catd K A) (@Const_func K Cat_cat B));
assertnot [A B C : Cat] (F : τ (Functor B C))
  (b : τ (Obj B)) (c : τ (Obj C)) ⊢
  @eq_refl (Functor A C) (@Const_func A C c)
  : τ (@= (Functor A C)
      (@Hom_fapp0 Cat_cat A A B C (@id Cat_cat A) F (@Const_func A B b))
      (@Const_func A C c));
assertnot [A B : Cat] (G : τ (Functor B A)) (C D : Cat) ⊢
  @eq_refl (Functor B Cat_cat) (@Const_catd B D)
  : τ (@= (Functor B Cat_cat)
      (@Hom_fapp0 Cat_cat A B Cat_cat Cat_cat G (@id Cat_cat Cat_cat)
        (@Const_catd A C)) (@Const_catd B D));
