/*
  Reviewer milestone: dependent homs and displayed laxity.

  These checks show the current endpoint-normal-form story: Sigma homs route
  through `homd_`; displayed internal action exposes `fdapp1_int_cell`; and
  ordinary post/left and pre/right witnesses are projections of that same
  whole action rather than independent naturality squares.
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

// Fixing the source of an ordinary transfor gives the post/left whole
// witness; its component is the displayed internal-action cell.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z)) (f : τ (Hom A X Y)) ⊢
  @tapp1_post_laxity_cell A B F G epsilon X Y Z g f
  ≡ @fdapp1_int_cell
      A
      (@hom_ A A (@id_func A) X)
      (@hom_ B A G (@fapp0 A B F X))
      (@tapp1_at_transf A B F G X epsilon)
      Y Z g f;

// Fixing the target and passing through Op(A) gives the pre/right mirror.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X)) (q : τ (Hom A X Y)) ⊢
  @tapp1_pre_laxity_cell A B F G epsilon W X Y h q
  ≡ @fdapp1_int_cell
      (Op_cat A)
      (@hom_con A Y A (@id_func A))
      (@hom_con B (@fapp0 A B G Y) A F)
      (@tapp1_con_at_transf A B F G epsilon Y)
      X W h q;

// Composition preservation is the identity-transfor specialization of the
// same post/left cell, yielding the normal-lax compositor surface.
assert [A B : Cat] (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z)) (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor A B F X Y Z g f
  ≡ @tapp1_post_laxity_cell
      A B F F (@id (Functor_cat A B) F) X Y Z g f;
