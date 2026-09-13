/* TEST ONLY: the whole local-y restriction evaluates the actual M. */
require open emdash.native_y_context;
assert [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  (M : τ (Functor (@native_index_cat Z D x) Cat_cat))
  (v : τ (Obj (Fibre_cat D y))) (a : τ (Hom Z x y)) ⊢
  fapp0 (fapp0 (fapp0 (@native_y_restriction_func Z D x y) M) v) a
  ≡ @fapp0 (@native_index_cat Z D x) Cat_cat M (Struct_sigma (Struct_sigma y v) a);
