/* TEST ONLY: the corrected local classifier still requires a different
   D-base. Pointwise transpose changes the intended v-fibre as well. */
require open emdash.emdash3_2;

// TEST ONLY: the rejected pointwise-transpose input substitution.
symbol test_transpose_family [K : Cat] (E : τ (Catd K))
  : τ (Catd (CoOnly2_cat K))
≔ @comp_cat_fapp0 (CoOnly2_cat K) (CoOnly2_cat Cat_cat) Cat_cat
    native_transpose_universe (@CoOnly2_func K Cat_cat E);

assert [Z : Cat] ⊢ Transpose_cat (Reverse12_cat Z) ≡ CoOnly2_cat Z;
assertnot [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Functor_catd (Reverse12_cat Z) D
    (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
      (@HomPresheaf_catd_func Z) x)
  : τ (Catd (Reverse12_cat Z));
assert [Z : Cat] (D : τ (Catd Z)) (x : τ (Obj Z)) ⊢
  @Functor_catd (Reverse12_cat Z) (@test_transpose_family Z D)
    (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
      (@HomPresheaf_catd_func Z) x)
  : τ (Catd (Reverse12_cat Z));
assert [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z)) ⊢
  @fapp0 (Reverse12_cat Z) Cat_cat
    (@Functor_catd (Reverse12_cat Z) (@test_transpose_family Z D)
      (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x)) y
  ≡ Functor_cat (Transpose_cat (Fibre_cat D y))
      (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat);
assertnot [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z)) ⊢
  @fapp0 (Reverse12_cat Z) Cat_cat
    (@Functor_catd (Reverse12_cat Z) (@test_transpose_family Z D)
      (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x)) y
  ≡ Functor_cat (Fibre_cat D y)
      (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat);
