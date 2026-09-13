/* TEST ONLY: inspect the canonical whole-y value before selecting its fold. */
require open emdash.emdash3_2;
symbol test_y_native_value [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E)) (x : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) (y : τ (Obj Z))
  : τ (Functor (Fibre_cat D y)
      (Functor_cat (Transpose_cat (Hom_cat Z x y)) Cat_cat))
≔ fapp0 (@native_y_restriction_func Z D x y) (@homd_src_sec Z D E FF x u);
flag "print_implicits" off;
flag "print_domains" off;
compute @test_y_native_value;
