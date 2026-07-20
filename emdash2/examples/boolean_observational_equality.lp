/*
  Reviewer milestone: visible-constructor Boolean observational equality.

  The four closed constructor pairs expose the Unit/Empty classifier matrix.
  Generic `eq_refl` remains the runtime reflexivity presentation even though
  its closed type reduces to Unit; existing J, path, Core, and categorical
  encoder owners therefore keep computing without a Boolean-specific registry.
  These checks do not claim open Boolean canonicity, equality reflection, or
  proof erasure to the native singleton constructor `tt`.
*/

require open emdash.emdash3_2;

assert ⊢ @= Bool_grpd false false ≡ Unit_grpd;

assert ⊢ @= Bool_grpd false true ≡ Empty_grpd;

assert ⊢ @= Bool_grpd true false ≡ Empty_grpd;

assert ⊢ @= Bool_grpd true true ≡ Unit_grpd;

assert ⊢ @eq_refl Bool_grpd false : τ Unit_grpd;

assert ⊢ @eq_refl Bool_grpd true : τ Unit_grpd;

assert
  (P : Π b : τ Bool_grpd, τ (@= Bool_grpd b false) → Grpd)
  (u : τ (P false (@eq_refl Bool_grpd false))) ⊢
  @ind_eqr
    Bool_grpd false P u false (@eq_refl Bool_grpd false)
  ≡ u;

assert
  (P : Π b : τ Bool_grpd, τ (@= Bool_grpd b true) → Grpd)
  (u : τ (P true (@eq_refl Bool_grpd true))) ⊢
  @ind_eqr
    Bool_grpd true P u true (@eq_refl Bool_grpd true)
  ≡ u;

assert ⊢
  @path_sym Bool_grpd false false (@eq_refl Bool_grpd false)
  ≡ @eq_refl Bool_grpd false;

assert ⊢
  @path_to_hom
    (Path_cat Bool_grpd)
    true true (@eq_refl Bool_grpd true)
  ≡ @id (Path_cat Bool_grpd) true;

assert ⊢
  @object_path_equiv_EQ1
    (Path_cat Bool_grpd) false false (@eq_refl Bool_grpd false)
  ≡ @omega_equiv_refl_EQ1 (Path_cat Bool_grpd) false;

// Local conversion and typing controls only; these are not canonicity or
// non-derivability theorems.
assertnot ⊢ false ≡ true;

assertnot ⊢ @eq_refl Bool_grpd false ≡ tt;

assertnot ⊢
  @ind_eqr
    Bool_grpd false
    (λ b : τ Bool_grpd,
      λ _ : τ (@= Bool_grpd b false), Unit_grpd)
    tt false tt
  ≡ tt;

assertnot ⊢
  @path_sym Bool_grpd false false tt
  ≡ tt;

assertnot (b : τ Bool_grpd) ⊢
  @= Bool_grpd b b
  ≡ Unit_grpd;

assertnot (b : τ Bool_grpd) ⊢
  @eq_refl Bool_grpd b
  : τ Unit_grpd;
