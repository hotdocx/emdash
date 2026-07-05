/*
  Reviewer milestone: products, evaluation, curry, and uncurry.

  These checks show the ordinary functional-programming layer: evaluation is a
  functor, fixed-point evaluation folds to object application, and curry/uncurry
  normalize through the generic hom-action owners.
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
    ≡ @fapp0 B C
        (@fapp0
          A
          (Functor_cat B C)
          (@hom_postcomp_fapp0
            Cat_cat
            Cat_cat
            (@id Cat_cat Cat_cat)
            A
            (Product_cat (Functor_cat B A) (Functor_cat B B))
            (Functor_cat B C)
            (@hom_postcomp_func
              Cat_cat
              Cat_cat
              (@id Cat_cat Cat_cat)
              B
              (Product_cat A B)
              C
              F)
            (@Product_pair_tele_func A B))
          x)
        y;

assert [A B C : Cat]
  (G : τ (Functor A (Functor_cat B C)))
  (x : τ (Obj A))
  (y : τ (Obj B)) ⊢
  fapp0 (uncurry_func G) (Struct_sigma x y)
    ≡ @fapp0
        (Product_cat A B)
        C
        (@hom_postcomp_fapp0
          Cat_cat
          Cat_cat
          (@id Cat_cat Cat_cat)
          (Product_cat A B)
          (Product_cat (Functor_cat B C) B)
          C
          (@Eval_func B C)
          (@Product_cat_fapp1_tapp0_func A (Functor_cat B C) B G))
        (Struct_sigma x y);
