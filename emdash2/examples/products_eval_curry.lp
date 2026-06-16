/*
  Reviewer milestone: products, evaluation, curry, and uncurry.

  These checks show the ordinary functional-programming layer: evaluation is a
  functor, fixed-point evaluation folds to object application, and curry/uncurry
  compute on objects.
*/

require open emdash.emdash3_2;

assert [A B : Cat] (F : τ (Functor A B)) (x : τ (Obj A)) ⊢
  fapp0 (@Eval_func A B) (Struct_sigma F x)
    ≡ fapp0 F x;

assert [A B : Cat] (x : τ (Obj A)) ⊢
  @comp_cat_fapp0
    (Functor_cat A B)
    (Product_cat (Functor_cat A B) A)
    B
    (@Eval_func A B)
    (@Eval_at_func A B x)
  ≡ @fapp0_func A B x;

assert [A B C : Cat]
  (F : τ (Functor (Product_cat A B) C))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  @fapp0 B C
    (@fapp0 A (Functor_cat B C) (@curry_func A B C F) x)
    y
    ≡ @fapp0 (Product_cat A B) C F (Struct_sigma x y);

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  fapp0 (uncurry_func G) (Struct_sigma x y)
    ≡ fapp0 (fapp0 G x) y;
