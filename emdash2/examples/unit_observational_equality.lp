/*
  Reviewer milestone: visible-constructor Unit observational equality.

  The closed `tt = tt` classifier computes to Unit while generic `eq_refl`
  retains its proof provenance. Existing literal-reflexivity consumers keep
  computing without a Unit registry; raw `tt` is not silently promoted to a
  second path-induction or proof-time beta. These checks do not claim Unit eta,
  canonicity, equality reflection, or arbitrary structural action.
*/

require open emdash.emdash3_2;

assert ⊢ @= Unit_grpd tt tt ≡ Unit_grpd;

assert ⊢ @eq_refl Unit_grpd tt : τ Unit_grpd;

assert ⊢ tt : τ (@= Unit_grpd tt tt);

assert
  (P : Π u : τ Unit_grpd, τ (@= Unit_grpd u tt) → Grpd)
  (v : τ (P tt (@eq_refl Unit_grpd tt))) ⊢
  @ind_eqr Unit_grpd tt P v tt (@eq_refl Unit_grpd tt)
  ≡ v;

assert ⊢
  @path_sym Unit_grpd tt tt (@eq_refl Unit_grpd tt)
  ≡ @eq_refl Unit_grpd tt;

assert ⊢
  @path_to_hom
    (Path_cat Unit_grpd) tt tt (@eq_refl Unit_grpd tt)
  ≡ @id (Path_cat Unit_grpd) tt;

assert ⊢
  @object_path_equiv_EQ1
    (Path_cat Unit_grpd) tt tt (@eq_refl Unit_grpd tt)
  ≡ @omega_equiv_refl_EQ1 (Path_cat Unit_grpd) tt;

// Local runtime, proof-time, and open-variable controls only.
assertnot ⊢ @eq_refl Unit_grpd tt ≡ tt;

assertnot ⊢
  @eq_refl Unit_grpd (@eq_refl Unit_grpd tt)
  : τ (@= Unit_grpd (@eq_refl Unit_grpd tt) tt);

assertnot ⊢
  @ind_eqr
    Unit_grpd tt
    (λ u : τ Unit_grpd,
      λ _ : τ (@= Unit_grpd u tt), Unit_grpd)
    tt tt tt
  ≡ tt;

assertnot ⊢ @path_sym Unit_grpd tt tt tt ≡ tt;

assertnot (u : τ Unit_grpd) ⊢
  @= Unit_grpd u u
  ≡ Unit_grpd;

assertnot (u : τ Unit_grpd) ⊢
  @eq_refl Unit_grpd u
  : τ Unit_grpd;
