/* NON-LIBRARY, TEST ONLY: typed observation of the expanded Hom order.
   Its comparison with the folded restricted Hom action is not qualified. */
require open emdash.native_homd_direct_owner_controls;
symbol test_native_homd_expanded_local_hom [Z : Cat] [D E : τ (Catd Z)]
  (FF : τ (Functord D E)) (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x))) (v : τ (Obj (Fibre_cat D y)))
  (a b : τ (Hom Z x y))
  : τ (Functor (Hom_cat (Transpose_cat (Hom_cat Z x y)) a b)
      (Functor_cat
        (fapp0 (@homd_ Z D E FF x u y v) a)
        (fapp0 (@homd_ Z D E FF x u y v) b)))
≔ @comp_cat_fapp0 (Hom_cat (Transpose_cat (Hom_cat Z x y)) a b)
    (Hom_cat (@native_index_cat Z D x)
      (Struct_sigma (Struct_sigma y v) a)
      (Struct_sigma (Struct_sigma y v) b))
    (Functor_cat
      (fapp0 (@homd_ Z D E FF x u y v) a)
      (fapp0 (@homd_ Z D E FF x u y v) b))
    (@fapp1_func (@native_index_cat Z D x) Cat_cat
      (@homd_src_sec Z D E FF x u)
      (Struct_sigma (Struct_sigma y v) a)
      (Struct_sigma (Struct_sigma y v) b))
    (@fapp1_func (Transpose_cat (Hom_cat Z x y)) (@native_index_cat Z D x)
      (@test_native_local_arrow_func Z D x y v) a b);
flag "print_implicits" off;
flag "print_domains" off;
compute @test_native_homd_expanded_local_hom;
