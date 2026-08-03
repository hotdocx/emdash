require open emdash.emdash3_2;
require open emdash.emdash3_2_eq1_hom_action;

// The selected left inverse also carries a whole right cancellation law.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @omega_equiv_along_cat_left_inv_right_law A B F u
  : τ (@=
      (Obj (Functor_cat B B))
      (@comp_cat_fapp0
        B A B
        F
        (@omega_equiv_along_left_inv Cat_cat A B F u))
      (@id_func B));

// The extension exposes one transparent package constructor to consumers.
symbol consume_omega_equiv_along_fapp1
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y))
≔ omega_equiv_along_fapp1 u x y;

// Both package inverse projections compute to the same selected inverse.
assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (omega_equiv_along_fapp1 u x y)
  ≡ @omega_equiv_along_right_inv
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
    (@fapp1_func A B F x y)
    (omega_equiv_along_fapp1 u x y);

// At a reflexive category equivalence the selected hom inverse normalizes to
// the identity hom functor, exercising the protected transparent proof chain.
assert [A : Cat] (x y : τ (Obj A)) ⊢
  @omega_equiv_along_left_inv
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat A x y)
    (@fapp1_func A A (@id_func A) x y)
    (omega_equiv_along_fapp1
      (@omega_equiv_along_refl Cat_cat A)
      x y)
  ≡ @id_func (Hom_cat A x y);
