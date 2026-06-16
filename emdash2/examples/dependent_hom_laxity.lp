/*
  Reviewer milestone: dependent homs and displayed laxity.

  These checks show the current endpoint-normal-form story: Sigma homs route
  through `homd_`, and identity-specialized displayed hom-action exposes the
  component-level laxity cell `fdapp1_int_cell`.
*/

require open emdash.emdash3_2;

assert [Z : Cat] (E : τ (Catd Z))
  (x y : τ (Obj Z))
  (u : τ (Obj (Fibre_cat E x)))
  (v : τ (Obj (Fibre_cat E y))) ⊢
  Hom_cat (@Sigma_cat Z E) (Struct_sigma x u) (Struct_sigma y v)
    ≡ Op_cat
        (@Sigma_cat
          (Op_cat (Hom_cat Z x y))
          (@homd_ Z E E (@id_funcd Z E) x u y v));

assert [K : Cat] (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x y : τ (Obj K))
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @tdapp1_int_cell
      K E D FF FF (@id_transfd K E D FF) x y p u
    ≡ @fdapp1_int_cell K E D FF x y p u;
