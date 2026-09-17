/* Proof-time constant-postcomposition view and its scope boundaries. */
require open emdash.emdash3_2_one_cat_adjunction_family_views;
// catalog-area: Whole arrow-family categorical isomorphisms

assert [B A C : Cat] (F : τ (Functor B A)) (t : τ (Obj C)) ⊢
  @eq_refl (Functor B C)
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) B A C (@Const_func A C t) F)
  : τ (@= (Functor B C)
      (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) B A C (@Const_func A C t) F)
      (@Const_func B C t));
assertnot [B A C : Cat] (F : τ (Functor B A)) (t u : τ (Obj C)) ⊢
  @eq_refl (Functor B C)
    (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) B A C (@Const_func A C t) F)
  : τ (@= (Functor B C)
      (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) B A C (@Const_func A C t) F)
      (@Const_func B C u));
assertnot [B A C : Cat] (F : τ (Functor B A)) (t : τ (Obj C)) ⊢
  @hom_postcomp_fapp0 Cat_cat Cat_cat (@id Cat_cat Cat_cat) B A C (@Const_func A C t) F
  ≡ @Const_func B C t;
