/* NON-LIBRARY controls for the copied HomPresheaf candidate. */
/* TEST ONLY: the candidate changes a defined classifier composition.
   These assertions add no operation, primitive, rewrite or unifier. */
require open emdash.emdash3_2;

assert [A B : Cat] (x : τ (Obj A)) (y : τ (Obj B)) ⊢
  @fapp0 (Product_cat (CoAbove3_cat A) (CoAbove3_cat B))
    (CoAbove3_cat (Product_cat A B))
    (@native_shift_product_intro A B) (Struct_sigma x y)
  ≡ @Product_pair A B x y;

assert (C : Cat) ⊢
  @fapp0 (Reverse12_cat Cat_cat) Cat_cat native_presheaf_universe C
  ≡ Functor_cat (Transpose_cat C) Cat_cat;

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  @fapp0 (Product_cat (CoOnly2_cat Z) (Reverse12_cat Z)) Cat_cat
    (@native_hom_presheaf_bifunctor Z) (Struct_sigma x y)
  ≡ Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat;

assert [Z : Cat] ⊢ @HomPresheaf_catd_func Z
  : τ (Functor (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z)));

assert [Z : Cat] (x y : τ (Obj Z)) ⊢
  @fapp0 (Reverse12_cat Z) Cat_cat
    (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
      (@HomPresheaf_catd_func Z) x) y
  ≡ Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat;

// The actual native endpoint now inhabits the computed presheaf fibre.
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat D y))) ⊢
  @homd_ Z D E FF x u y v
  : τ (Obj (@fapp0 (Reverse12_cat Z) Cat_cat
      (@fapp0 (CoOnly2_cat Z) (Catd_cat (Reverse12_cat Z))
        (@HomPresheaf_catd_func Z) x) y));
