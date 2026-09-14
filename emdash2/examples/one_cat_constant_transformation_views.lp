require open emdash.emdash3_2_one_cat_constant_transformation_views;
symbol K : Cat;
symbol A : Cat;
symbol B : Cat;
symbol B1 : τ (IsNCat (cat_succ cat_zero) B);
symbol F : τ (Functor A B);
symbol x : τ (Obj A);
symbol y : τ
  (Obj A);
symbol f : τ (Hom A x y);
symbol f2 : τ (Hom A x y);
symbol theta : τ (@Transf A B F F);

// Typed reflexivity exercises the proof-time constant postcomposition view.
assert ⊢ @eq_refl (@Transf K B (@Const_func K B (@fapp0 A B F x)) (@Const_func K B (@fapp0 A B F y)))
  (@comp_prod_fapp1_fapp0 Cat_cat K A B (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A x) F)
  (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A y) F) (@Product_pair_grpd (@Transf K A
  (@Const_func K A x) (@Const_func K A y)) (@Transf A B F F) (@Const_transf K A x y f) (@id (Functor_cat A B)
  F))) : τ (@= (@Transf K B (@Const_func K B (@fapp0 A B F x)) (@Const_func K B (@fapp0 A B F y)))
  (@comp_prod_fapp1_fapp0 Cat_cat K A B (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A x) F)
  (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A y) F) (@Product_pair_grpd (@Transf K A
  (@Const_func K A x) (@Const_func K A y)) (@Transf A B F F) (@Const_transf K A x y f) (@id (Functor_cat A B)
  F))) (@Const_transf K B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp1_fapp0 A B F x y f)));
// Retain the original arrow; the functor is an unchanged rigid parameter.
assertnot ⊢ @eq_refl (@Transf K B (@Const_func K B (@fapp0 A B F x)) (@Const_func K B (@fapp0 A B F y)))
  (@comp_prod_fapp1_fapp0 Cat_cat K A B (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A x) F)
  (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A y) F) (@Product_pair_grpd (@Transf K A
  (@Const_func K A x) (@Const_func K A y)) (@Transf A B F F) (@Const_transf K A x y f) (@id (Functor_cat A B)
  F))) : τ (@= (@Transf K B (@Const_func K B (@fapp0 A B F x)) (@Const_func K B (@fapp0 A B F y)))
  (@comp_prod_fapp1_fapp0 Cat_cat K A B (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A x) F)
  (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A y) F) (@Product_pair_grpd (@Transf K A
  (@Const_func K A x) (@Const_func K A y)) (@Transf A B F F) (@Const_transf K A x y f) (@id (Functor_cat A B)
  F))) (@Const_transf K B (@fapp0 A B F x) (@fapp0 A B F y) (@fapp1_fapp0 A B F x y f2)));
// A general second component is not the identity postcomposition case.
assertnot ⊢ @eq_refl (@Transf K B (@Const_func K B (@fapp0 A B F x)) (@Const_func K B (@fapp0 A B F y)))
  (@comp_prod_fapp1_fapp0 Cat_cat K A B (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A x) F)
  (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A y) F) (@Product_pair_grpd (@Transf K A
  (@Const_func K A x) (@Const_func K A y)) (@Transf A B F F) (@Const_transf K A x y f) theta)) : τ (@=
  (@Transf K B (@Const_func K B (@fapp0 A B F x)) (@Const_func K B (@fapp0 A B F y))) (@comp_prod_fapp1_fapp0
  Cat_cat K A B (@Product_pair_grpd (Functor K A) (Functor A B) (@Const_func K A x) F) (@Product_pair_grpd
  (Functor K A) (Functor A B) (@Const_func K A y) F) (@Product_pair_grpd (@Transf K A (@Const_func K A x)
  (@Const_func K A y)) (@Transf A B F F) (@Const_transf K A x y f) theta)) (@Const_transf K B (@fapp0 A B F x)
  (@fapp0 A B F y) (@fapp1_fapp0 A B F x y f)));
