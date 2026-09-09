/* Source identity normalization must not erase the exchanged-action cut. */
require open emdash.emdash3_2;
assert [A B C : Cat] (H : τ (Functor A (Functor_cat (Op_cat B) C))) (b : τ (Obj B)) ⊢
  @sym_tapp1_fapp0_transf A (Op_cat B) C H b b (@id B b)
  ≡ @id (Functor_cat A C) (@sym_fapp0_func A (Op_cat B) C H b);
assert [A B C : Cat] (H : τ (Functor A (Functor_cat (Op_cat B) C))) (b : τ (Obj B)) ⊢
  @fapp1_fapp0 (Op_cat B) (Functor_cat A C) (@sym_func A (Op_cat B) C H) b b (@id (Op_cat B) b)
  ≡ @id (Functor_cat A C) (@sym_fapp0_func A (Op_cat B) C H b);
assert [A B C : Cat] (H : τ (Functor A (Functor_cat (Op_cat B) C))) (b : τ (Obj B)) (a : τ (Obj A)) ⊢
  @tapp0_fapp0 _ _ _ _ a (@sym_tapp1_fapp0_transf A (Op_cat B) C H b b (@id B b))
  ≡ @id C (@fapp0 (Op_cat B) C (@fapp0 A (Functor_cat (Op_cat B) C) H a) b);
assertnot [A B C : Cat] (H : τ (Functor A (Functor_cat (Op_cat B) C))) (b : τ (Obj B)) (q : τ (Hom (Op_cat B) b b)) ⊢
  @sym_tapp1_fapp0_transf A (Op_cat B) C H b b q
  ≡ @id (Functor_cat A C) (@sym_fapp0_func A (Op_cat B) C H b);
