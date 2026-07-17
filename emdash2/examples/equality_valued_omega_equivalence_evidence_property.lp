require open emdash.emdash3_2;
require open emdash.emdash3_2_eq1_evidence_property;

/*
  Equality-valued fixed-arrow evidence is a real data structure with a
  transparent two-fibre view. Once inhabited, each fibre is contractible:
  ordinary composition with the forward arrow is an equivalence on inverse
  candidates. Thus evidence is proposition-valued in every category, without
  a decoder, axiom, or proof-erasure rule.
*/

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_EQ1 C x y f)) ⊢
  @omega_equiv_along_from_view_view_EQ1 C x y f u
  : τ (@=
      (@OmegaEquivAlong_EQ1 C x y f)
      (@omega_equiv_along_from_view_EQ1 C x y f
        (@omega_equiv_along_view_EQ1 C x y f u))
      u);

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_equiv_evidence_is_contr_EQ1 A y x p
  : τ (IsContr (@OmegaEquivAlong_EQ1 (Path_cat A) x y p));

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @path_equiv_evidence_is_prop_EQ1 A x y p
  : τ (IsPropGrpd (@OmegaEquivAlong_EQ1 (Path_cat A) x y p));

// The path theorem is a computational specialization of a dimension-free
// categorical result.
assert [C : Cat]
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @omega_equiv_along_evidence_is_prop_EQ1 C x y f
  : τ (IsPropGrpd (@OmegaEquivAlong_EQ1 C x y f));

// The selected centre at reflexivity is the canonical explicit package.
assert [A : Grpd]
  (x : τ A) ⊢
  is_contr_center (@path_refl_equiv_evidence_is_contr_EQ1 A x)
  ≡ @path_equiv_along_EQ1 A x x (@eq_refl A x);

// Contractibility is propositional structure, not judgmental proof erasure.
assertnot [A : Grpd]
  (x : τ A) ⊢
  is_contr_path
    (@path_refl_equiv_evidence_is_contr_EQ1 A x)
    (@path_equiv_along_EQ1 A x x (@eq_refl A x))
  ≡ @eq_refl
      (@OmegaEquivAlong_EQ1 (Path_cat A) x x (@eq_refl A x))
      (@path_equiv_along_EQ1 A x x (@eq_refl A x));

/*
  The earlier locally-set proof remains useful as a smaller independent
  derivation: inverse choices agree by associativity and unit laws, while law
  proofs agree because their ambient homs are sets.
*/
assert [C : Cat]
  (h : τ (@IsLocallySetCat_EQ1 C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @locally_set_equiv_evidence_is_prop_EQ1 C h x y f
  : τ (IsPropGrpd (@OmegaEquivAlong_EQ1 C x y f));

// Native finite-dimension recursion now proves the expected object-truncation
// bound at every finite directed dimension.
assert (n : CatDim) [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  @ncat_obj_trunc_EQ1 n C h
  : τ (IsObjTruncCat (cat_dim_trunc_level n) C);

// The readable one-category theorem is the corresponding specialization.
assert [C : Cat]
  (h : τ (IsNCat (cat_succ cat_zero) C)) ⊢
  @one_cat_obj_trunc_EQ1 C h
  : τ (IsObjTruncCat
      (cat_dim_trunc_level (cat_succ cat_zero)) C);
