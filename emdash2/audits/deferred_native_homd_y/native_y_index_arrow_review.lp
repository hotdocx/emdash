/* TEST ONLY: genuine local v and base-Hom arrows through the derived map. */
require open emdash.native_y_context;
symbol test_y_index_arrow [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  (v w : τ (Obj (Fibre_cat D y))) (a b : τ (Hom Z x y))
  (beta : τ (Hom (Fibre_cat D y) v w))
  (theta : τ (Hom (Hom_cat Z x y) b a))
  : τ (Hom (@native_index_cat Z D x)
      (Struct_sigma (Struct_sigma y v) a)
      (Struct_sigma (Struct_sigma y w) b))
≔ @fapp1_fapp0
    (Product_cat (Fibre_cat D y) (Transpose_cat (Hom_cat Z x y)))
    (@native_index_cat Z D x) (@native_y_index_func Z D x y)
    (Struct_sigma v a) (Struct_sigma w b) (Struct_sigma beta theta);
// Retyping the actual normal form checks the dependent triangle endpoint.
symbol test_y_index_arrow_expected [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  (v w : τ (Obj (Fibre_cat D y))) (a b : τ (Hom Z x y))
  (beta : τ (Hom (Fibre_cat D y) v w))
  (theta : τ (Hom (Hom_cat Z x y) b a))
  : τ (Hom (@native_index_cat Z D x)
      (Struct_sigma (Struct_sigma y v) a)
      (Struct_sigma (Struct_sigma y w) b))
≔ Struct_sigma (Struct_sigma (@id Z y) beta) theta;
assert ⊢ @test_y_index_arrow ≡ @test_y_index_arrow_expected;
flag "print_implicits" off;
flag "print_domains" off;
compute @test_y_index_arrow;
