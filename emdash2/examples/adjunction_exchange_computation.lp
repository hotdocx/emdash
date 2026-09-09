require open emdash.emdash3_2;

// Whole evaluation after exchange, before point application.
assert [A B C : Cat] (H : τ (Functor A (Functor_cat B C))) (a : τ (Obj A)) ⊢
  @comp_cat_fapp0 B (Functor_cat A C) C
    (@sym_fapp0_func (Functor_cat A C) A C (@id_func (Functor_cat A C)) a)
    (@sym_func A B C H)
  ≡ @fapp0 A (Functor_cat B C) H a;

// Reducible Functor_cat(A,X×Y) must not be a redundant identity guard.
assert [A B X Y : Cat] (H : τ (Functor A (Functor_cat B (Product_cat X Y)))) (a : τ (Obj A)) ⊢
  @comp_cat_fapp0 B (Functor_cat A (Product_cat X Y)) (Product_cat X Y)
    (@sym_fapp0_func (Functor_cat A (Product_cat X Y)) A (Product_cat X Y)
      (@id_func (Functor_cat A (Product_cat X Y))) a)
    (@sym_func A B (Product_cat X Y) H)
  ≡ @fapp0 A (Functor_cat B (Product_cat X Y)) H a;

// The whole equality retains arbitrary subsequent Hom action.
type λ A : Cat, λ B : Cat, λ C : Cat, λ H : τ (Functor A (Functor_cat B C)),
  λ a : τ (Obj A), λ x : τ (Obj B), λ y : τ (Obj B),
  @fapp1_func B C
    (@comp_cat_fapp0 B (Functor_cat A C) C
      (@sym_fapp0_func (Functor_cat A C) A C (@id_func (Functor_cat A C)) a)
      (@sym_func A B C H)) x y;
