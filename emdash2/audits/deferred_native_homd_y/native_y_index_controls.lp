/* TEST ONLY: whole local-index inclusion and its original coordinates. */
require open emdash.native_y_context;
assert [Z : Cat] (D : τ (Catd Z)) (x y : τ (Obj Z))
  (v : τ (Obj (Fibre_cat D y))) (a : τ (Hom Z x y)) ⊢
  @fapp0 (Product_cat (Fibre_cat D y) (Transpose_cat (Hom_cat Z x y)))
    (@native_index_cat Z D x) (@native_y_index_func Z D x y)
    (Struct_sigma v a)
  ≡ @Struct_sigma (Obj (CoAbove2_cat (@Sigma_cat Z D)))
      (λ d : τ (Obj (CoAbove2_cat (@Sigma_cat Z D))),
        Obj (@Fibre_cat (CoAbove2_cat (@Sigma_cat Z D))
          (@Op_catd (@Sigma_cat Z D) (@native_index_hom_catd Z D x)) d))
      (Struct_sigma y v) a;
