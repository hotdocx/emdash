require open emdash.emdash3_2_gray_profiles;
require emdash.emdash3_2_one_cat_adjunction_introduction;

// ambient: whole accumulation.
assertnot [A B : Cat] (F : τ (Functor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) ⊢
  (@comp_fapp0 Cat_cat (Hom_cat B (@fapp0 A B F Y) Z) (Hom_cat B (@fapp0 A B F X) Z) (Hom_cat B (@fapp0 A B F W) Z)
    (@hom_precomp_along_func A B F Z W X p)
    (@hom_precomp_along_func A B F Z X Y q)) ≡ (@hom_precomp_along_func A B F Z W Y (@comp_fapp0 A W X Y q p));

// ambient: nested point accumulation.
assertnot [A B : Cat] (F : τ (Functor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) (h : τ (Hom B (@fapp0 A B F Y) Z)) ⊢
  (@hom_precomp_along_fapp0 A B F Z W X p
    (@hom_precomp_along_fapp0 A B F Z X Y q h)) ≡ (@hom_precomp_along_fapp0 A B F Z W Y (@comp_fapp0 A W X Y q p) h);

assertnot [A B : Cat] (F : τ (Functor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) ⊢
  @eq_refl (Functor (Hom_cat B (@fapp0 A B F Y) Z) (Hom_cat B (@fapp0 A B F W) Z)) (@hom_precomp_along_func A B F Z W Y (@comp_fapp0 A W X Y q p))
  : τ (@= (Functor (Hom_cat B (@fapp0 A B F Y) Z) (Hom_cat B (@fapp0 A B F W) Z)) (@comp_fapp0 Cat_cat (Hom_cat B (@fapp0 A B F Y) Z) (Hom_cat B (@fapp0 A B F X) Z) (Hom_cat B (@fapp0 A B F W) Z)
    (@hom_precomp_along_func A B F Z W X p)
    (@hom_precomp_along_func A B F Z X Y q)) (@hom_precomp_along_func A B F Z W Y (@comp_fapp0 A W X Y q p)));

assertnot [A B : Cat] (F : τ (Functor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) (h : τ (Hom B (@fapp0 A B F Y) Z)) ⊢
  @eq_refl (Hom B (@fapp0 A B F W) Z) (@hom_precomp_along_fapp0 A B F Z W Y (@comp_fapp0 A W X Y q p) h)
  : τ (@= (Hom B (@fapp0 A B F W) Z) (@hom_precomp_along_fapp0 A B F Z W X p
    (@hom_precomp_along_fapp0 A B F Z X Y q h)) (@hom_precomp_along_fapp0 A B F Z W Y (@comp_fapp0 A W X Y q p) h));

// strict: whole accumulation.
assert [A B : Cat] (S : τ (@StrictFunctor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) ⊢
  (@comp_fapp0 Cat_cat (Hom_cat B (@fapp0 A B (@strict_functor A B S) Y) Z) (Hom_cat B (@fapp0 A B (@strict_functor A B S) X) Z) (Hom_cat B (@fapp0 A B (@strict_functor A B S) W) Z)
    (@hom_precomp_along_func A B (@strict_functor A B S) Z W X p)
    (@hom_precomp_along_func A B (@strict_functor A B S) Z X Y q)) ≡ (@hom_precomp_along_func A B (@strict_functor A B S) Z W Y (@comp_fapp0 A W X Y q p));

// strict: nested point accumulation.
assert [A B : Cat] (S : τ (@StrictFunctor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) (h : τ (Hom B (@fapp0 A B (@strict_functor A B S) Y) Z)) ⊢
  (@hom_precomp_along_fapp0 A B (@strict_functor A B S) Z W X p
    (@hom_precomp_along_fapp0 A B (@strict_functor A B S) Z X Y q h)) ≡ (@hom_precomp_along_fapp0 A B (@strict_functor A B S) Z W Y (@comp_fapp0 A W X Y q p) h);

// Both evaluation orders retain the selected computation.
assert [A B : Cat] (S : τ (@StrictFunctor A B)) [W X Y : τ (Obj A)] [Z : τ (Obj B)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) (h : τ (Hom B (@fapp0 A B (@strict_functor A B S) Y) Z)) ⊢
  @fapp0 (Hom_cat B (@fapp0 A B (@strict_functor A B S) Y) Z) (Hom_cat B (@fapp0 A B (@strict_functor A B S) W) Z) (@comp_fapp0 Cat_cat (Hom_cat B (@fapp0 A B (@strict_functor A B S) Y) Z) (Hom_cat B (@fapp0 A B (@strict_functor A B S) X) Z) (Hom_cat B (@fapp0 A B (@strict_functor A B S) W) Z)
    (@hom_precomp_along_func A B (@strict_functor A B S) Z W X p)
    (@hom_precomp_along_func A B (@strict_functor A B S) Z X Y q)) h ≡ (@hom_precomp_along_fapp0 A B (@strict_functor A B S) Z W Y (@comp_fapp0 A W X Y q p) h);

// identity: whole accumulation.
assert [A : Cat] [W X Y : τ (Obj A)] [Z : τ (Obj A)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) ⊢
  (@comp_fapp0 Cat_cat (Hom_cat A (@fapp0 A A (@id_func A) Y) Z) (Hom_cat A (@fapp0 A A (@id_func A) X) Z) (Hom_cat A (@fapp0 A A (@id_func A) W) Z)
    (@hom_precomp_along_func A A (@id_func A) Z W X p)
    (@hom_precomp_along_func A A (@id_func A) Z X Y q)) ≡ (@hom_precomp_along_func A A (@id_func A) Z W Y (@comp_fapp0 A W X Y q p));

// identity: nested point accumulation.
assert [A : Cat] [W X Y : τ (Obj A)] [Z : τ (Obj A)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) (h : τ (Hom A (@fapp0 A A (@id_func A) Y) Z)) ⊢
  (@hom_precomp_along_fapp0 A A (@id_func A) Z W X p
    (@hom_precomp_along_fapp0 A A (@id_func A) Z X Y q h)) ≡ (@hom_precomp_along_fapp0 A A (@id_func A) Z W Y (@comp_fapp0 A W X Y q p) h);

// Both evaluation orders retain the selected computation.
assert [A : Cat] [W X Y : τ (Obj A)] [Z : τ (Obj A)]
  (p : τ (Hom A W X)) (q : τ (Hom A X Y)) (h : τ (Hom A (@fapp0 A A (@id_func A) Y) Z)) ⊢
  @fapp0 (Hom_cat A (@fapp0 A A (@id_func A) Y) Z) (Hom_cat A (@fapp0 A A (@id_func A) W) Z) (@comp_fapp0 Cat_cat (Hom_cat A (@fapp0 A A (@id_func A) Y) Z) (Hom_cat A (@fapp0 A A (@id_func A) X) Z) (Hom_cat A (@fapp0 A A (@id_func A) W) Z)
    (@hom_precomp_along_func A A (@id_func A) Z W X p)
    (@hom_precomp_along_func A A (@id_func A) Z X Y q)) h ≡ (@hom_precomp_along_fapp0 A A (@id_func A) Z W Y (@comp_fapp0 A W X Y q p) h);
