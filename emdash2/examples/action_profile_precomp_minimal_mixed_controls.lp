require open emdash.emdash3_2_gray_profiles;
require emdash.emdash3_2_one_cat_adjunction_introduction;

// The staged unqualified theorem must now be rejected at its owning cut.
assertnot [A B : Cat] (F : τ (Functor A B))
  [V W X : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A V W)) (g : τ (Hom B (@fapp0 A B F X) Z)) ⊢
  @eq_refl (Hom B (@fapp0 A B F V) Z)
    (@hom_precomp_along_fapp0 A B F Z V X (@comp_fapp0 A V W X p q) g)
  : τ (@= (Hom B (@fapp0 A B F V) Z)
      (@comp_fapp0 B (@fapp0 A B F V) (@fapp0 A B F W) Z
        (@hom_precomp_along_fapp0 A B F Z W X p g) (@fapp1_fapp0 A B F V W q))
      (@hom_precomp_along_fapp0 A B F Z V X (@comp_fapp0 A V W X p q) g));

// Arbitrary g stays opaque: this observes the actual strict-profile fold.
assert [A B : Cat] (S : τ (@StrictFunctor A B))
  [V W X : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A V W))
  (g : τ (Hom B (@fapp0 A B (@strict_functor A B S) X) Z)) ⊢
  @comp_fapp0 B (@fapp0 A B (@strict_functor A B S) V)
    (@fapp0 A B (@strict_functor A B S) W) Z
    (@hom_precomp_along_fapp0 A B (@strict_functor A B S) Z W X p g)
    (@fapp1_fapp0 A B (@strict_functor A B S) V W q)
  ≡ @hom_precomp_along_fapp0 A B (@strict_functor A B S) Z V X
      (@comp_fapp0 A V W X p q) g;

assertnot [A : Cat] [V W X Z : τ (Obj A)]
  (p : τ (Hom A W X)) (q : τ (Hom A V W)) (g : τ (Hom A X Z)) ⊢
  @comp_fapp0 A V W Z (@hom_precomp_along_fapp0 A A (@id_func A) Z W X p g) q
  ≡ @hom_precomp_along_fapp0 A A (@id_func A) Z V X (@comp_fapp0 A V W X p q) g;
