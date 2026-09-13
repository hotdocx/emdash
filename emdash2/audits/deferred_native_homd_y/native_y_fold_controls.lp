/* TEST ONLY: whole y-restriction reaches the existing native local owner. */
require open emdash.emdash3_2;
assert [Z : Cat] [D E : τ (Catd Z)] (FF : τ (Functord D E))
  (x y : τ (Obj Z)) (u : τ (Obj (Fibre_cat E x))) ⊢
  fapp0 (@native_y_restriction_func Z D x y) (@homd_src_sec Z D E FF x u)
  ≡ @homd_tgt_func Z D E FF x u y;
