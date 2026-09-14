/* Whole coherence in genuine groupoidal/discrete scope, with no extra beta. */
require open emdash.emdash3_2_discrete_functor_paths;

assert [A B : Cat] (A0 : τ (IsGroupoidalCat A))
  (f : τ (@Function_grpd (Obj A) (Obj B))) (a : τ (Obj A))
  ⊢ @groupoidal_object_map_point A B A0 f a
    : τ (@= (Obj B) (@fapp0 A B (@groupoidal_object_map_func A B A0 f) a) (f a));
assert [A B : Cat] (A0 : τ (IsGroupoidalCat A))
  (f : τ (@Function_grpd (Obj A) (Obj B))) (x y : τ (Obj A))
  ⊢ @fapp1_func A B (@groupoidal_object_map_func A B A0 f) x y
    : τ (Functor (Hom_cat A x y) (Hom_cat B
      (@fapp0 A B (@groupoidal_object_map_func A B A0 f) x)
      (@fapp0 A B (@groupoidal_object_map_func A B A0 f) y)));
assert [A B : Cat] (B0 : τ (IsDiscreteCat B)) (F G : τ (Functor A B))
  (p : Π x : τ (Obj A), τ (@= (Obj B) (@fapp0 A B F x) (@fapp0 A B G x)))
  ⊢ @discrete_pointwise_transf A B B0 F G p : τ (@Transf A B F G);
assert [A B : Cat] (B0 : τ (IsDiscreteCat B)) (F G : τ (Functor A B))
  (p : Π x : τ (Obj A), τ (@= (Obj B) (@fapp0 A B F x) (@fapp0 A B G x)))
  ⊢ @discrete_functor_path A B B0 F G p : τ (@= (Functor A B) F G);
assertnot [A B : Cat] (A0 : τ (IsGroupoidalCat A))
  (f : τ (@Function_grpd (Obj A) (Obj B))) (a : τ (Obj A))
  ⊢ @fapp0 A B (@groupoidal_object_map_func A B A0 f) a ≡ f a;
assertnot [A B : Cat] (B0 : τ (IsDiscreteCat B))
  ⊢ @discrete_functor_category A B B0 : τ (IsDiscreteCat A);
assertnot [A B : Cat] (B0 : τ (IsDiscreteCat B)) (F G : τ (Functor A B))
  ⊢ @eq_refl (Functor A B) F : τ (@= (Functor A B) F G);
