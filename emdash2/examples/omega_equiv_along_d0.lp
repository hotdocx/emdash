/*
  Reviewer milestone: frozen Candidate-D0 fixed-arrow omega-equivalence
  evidence. This is one of seven permitted compatibility consumers.

  The primary certificate is indexed by an already-selected arrow. Its
  first-class form is a transparent Sigma package, while inverse cells return
  the same new package recursively in the next hom-category. This staging
  owner is independent of the old public OmegaEquiv interface; variable
  functor hom action and the public migration remain later gates.
*/

require open emdash.emdash3_2;
require open emdash.emdash3_2_legacy_compat;

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @Struct_sigma
    (Hom C x y)
    (λ g : τ (Hom C x y), @OmegaEquivAlong_D0 C x y g)
    f
    u
  : τ (OmegaEquiv_D0 C x y);

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_to_D0 C x y
    (@Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong_D0 C x y g)
      f
      u)
  ≡ f;

assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y))
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_evidence_D0 C x y
    (@Struct_sigma
      (Hom C x y)
      (λ g : τ (Hom C x y), @OmegaEquivAlong_D0 C x y g)
      f
      u)
  ≡ u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_cell_D0 C x y f u
  : τ (OmegaEquiv_D0
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f)
      (@id C x));

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_right_cell_D0 C x y f u
  : τ (OmegaEquiv_D0
      (Hom_cat C y y)
      (@comp_fapp0 C y x y
        f
        (@omega_equiv_along_right_inv_D0 C x y f u))
      (@id C y));

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_to_D0 C x x (@omega_equiv_refl_D0 C x)
  ≡ @id C x;

assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_cell_D0
    C x x (@id C x)
    (@omega_equiv_along_refl_D0 C x)
  ≡ @omega_equiv_refl_D0
      (Hom_cat C x x)
      (@id C x);

// The left reflexive cell remains observable after one recursive hom step.
assert [C : Cat]
  (x : τ (Obj C)) ⊢
  @omega_equiv_along_left_cell_D0
    (Hom_cat C x x)
    (@id C x)
    (@id C x)
    (@id (Hom_cat C x x) (@id C x))
    (@omega_equiv_evidence_D0
      (Hom_cat C x x)
      (@id C x)
      (@id C x)
      (@omega_equiv_along_left_cell_D0
        C x x (@id C x)
        (@omega_equiv_along_refl_D0 C x)))
  ≡ @omega_equiv_refl_D0
      (Hom_cat (Hom_cat C x x) (@id C x) (@id C x))
      (@id (Hom_cat C x x) (@id C x));

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv_D0 C x y)) ⊢
  @Struct_sigma
    (Hom C x y)
    (λ f : τ (Hom C x y), @OmegaEquivAlong_D0 C x y f)
    (@omega_equiv_to_D0 C x y e)
    (@omega_equiv_evidence_D0 C x y e)
  ≡ e;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @comp_fapp0 C x y x
    (@omega_equiv_along_left_inv_D0 C x y f u)
    f
  ≡ @id C x;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @comp_fapp0 C y x y
    f
    (@omega_equiv_along_right_inv_D0 C x y f u)
  ≡ @id C y;
