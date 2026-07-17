/*
  Reviewer milestone: migration between D0 and equality-valued evidence.

  Old recursive D0 certificates can be observed as finite equality-law data.
  In the reverse direction, a temporary compatibility constructor targets the
  otherwise opaque D0 representation, but all of its public D0 observations
  are specified. Recursive cells are built from `object_path_equiv_EQ1`, not
  from the legacy `idtoequiv_cat` encoder. This constructor exists only to
  migrate old consumers; the new equality-valued foundation does not need D0.
*/

require open emdash.emdash3_2;

assert [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_inv_EQ1 C x y f
    (@omega_equiv_along_D0_to_EQ1 C x y f u)
  ≡ @omega_equiv_along_left_inv_D0 C x y f u;

assert [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_left_law_EQ1 C x y f
    (@omega_equiv_along_D0_to_EQ1 C x y f u)
  ≡ @omega_equiv_left_law C x y
      (@omega_equiv_from_along C x y f u);

assert [C : Cat] [x y : τ (Obj C)]
  (e : τ (OmegaEquiv_D0 C x y)) ⊢
  @omega_equiv_to_EQ1 C x y (@omega_equiv_D0_to_EQ1 C x y e)
  ≡ @omega_equiv_to_D0 C x y e;

assert [C : Cat] [x y : τ (Obj C)]
  (e : τ (@OmegaEquiv_EQ1 C x y)) ⊢
  @omega_equiv_to_D0 C x y (@omega_equiv_EQ1_to_D0 C x y e)
  ≡ @omega_equiv_to_EQ1 C x y e;

assert [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_along_right_inv_D0 C x y f
    (@omega_equiv_along_EQ1_to_D0 C x y f u)
  ≡ @omega_equiv_along_right_inv_EQ1 C x y f u;

// The recursive D0 cell is visibly reified from the equality law.
assert [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_along_left_cell_D0 C x y f
    (@omega_equiv_along_EQ1_to_D0 C x y f u)
  ≡ @omega_equiv_EQ1_to_D0
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_EQ1 C x y f u)
        f)
      (@id C x)
      (@object_path_equiv_EQ1
        (Hom_cat C x x)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_EQ1 C x y f u)
          f)
        (@id C x)
        (@omega_equiv_along_left_law_EQ1 C x y f u));

// Consequently its selected next-hom arrow computes through path_to_hom.
assert [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_to_D0
    (Hom_cat C x x)
    (@comp_fapp0 C x y x
      (@omega_equiv_along_left_inv_EQ1 C x y f u)
      f)
    (@id C x)
    (@omega_equiv_along_left_cell_D0 C x y f
      (@omega_equiv_along_EQ1_to_D0 C x y f u))
  ≡ @path_to_hom
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_EQ1 C x y f u)
        f)
      (@id C x)
      (@omega_equiv_along_left_law_EQ1 C x y f u);

assert [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_D0_to_EQ1
    C x x (@id C x) (@omega_equiv_along_refl_D0 C x)
  ≡ @omega_equiv_along_refl_EQ1 C x;

// One existing D0b consumer accepts new evidence through the bridge.
assert [A B : Cat] [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_EQ1 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  omega_equiv_along_left_inv_EQ1
    (omega_equiv_along_D0_to_EQ1
      (@omega_equiv_along_fapp1_D0 A B F
        (omega_equiv_along_EQ1_to_D0 u) x y))
  ≡ @omega_equiv_along_fapp1_left_inv_D0
      A B F (omega_equiv_along_EQ1_to_D0 u) x y;

// D0 lacks eta/extensionality, so the compatibility maps are not round-trip
// equivalences of evidence packages.
assertnot [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_EQ1_to_D0 C x y f
    (@omega_equiv_along_D0_to_EQ1 C x y f u)
  ≡ u;

assertnot [C : Cat] [x y : τ (Obj C)] [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_along_D0_to_EQ1 C x y f
    (@omega_equiv_along_EQ1_to_D0 C x y f u)
  ≡ u;

assertnot [C : Cat] (x : τ (Obj C)) ⊢
  @omega_equiv_along_EQ1_to_D0
    C x x (@id C x) (@omega_equiv_along_refl_EQ1 C x)
  ≡ @omega_equiv_along_refl_D0 C x;
