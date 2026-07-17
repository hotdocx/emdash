/*
  Reviewer milestone: directed object truncation conditional on certificate
  evidence property.

  The mathematical induction is executable without pretending that the
  current opaque fixed-arrow certificate has already been proved
  proposition-valued.
*/

require open emdash.emdash3_2;

assert ⊢ OmegaEquivAlongEvidenceProp_D0 : Grpd;

assert (P : τ OmegaEquivAlongEvidenceProp_D0)
  [C : Cat]
  (x y : τ (Obj C))
  (f : τ (Hom C x y)) ⊢
  P C x y f
  : τ (IsPropGrpd (@OmegaEquivAlong_D0 C x y f));

assert (n : CatDim)
  [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_cat_dim n A h
  : τ (IsTruncGrpd (cat_dim_trunc_level n) A);

assert [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @prop_is_trunc_cat_dim cat_zero A h
  ≡ @prop_is_trunc_succ trunc_minus_one A h;

assert (P : τ OmegaEquivAlongEvidenceProp_D0)
  (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  @ncat_obj_trunc_from_evidence_prop P n C h
  : τ (IsObjTruncCat (cat_dim_trunc_level n) C);

assert (P : τ OmegaEquivAlongEvidenceProp_D0)
  [C : Cat]
  (h : τ (IsNCat cat_zero C)) ⊢
  @ncat_obj_trunc_from_evidence_prop P cat_zero C h
  ≡ @is_discrete_cat_obj_set C h;

assert (P : τ OmegaEquivAlongEvidenceProp_D0)
  (X : τ ZeroCat) ⊢
  @ncat_obj_trunc_from_evidence_prop
    P
    cat_zero
    (@ncat_carrier cat_zero X)
    (@ncat_evidence cat_zero X)
  ≡ @is_discrete_cat_obj_set
      (@ncat_carrier cat_zero X)
      (@ncat_evidence cat_zero X);

assert (P : τ OmegaEquivAlongEvidenceProp_D0)
  (X : τ OneCat) ⊢
  @ncat_obj_trunc_from_evidence_prop
    P
    (cat_succ cat_zero)
    (@ncat_carrier (cat_succ cat_zero) X)
    (@ncat_evidence (cat_succ cat_zero) X)
  : τ (IsObjTruncCat
      trunc_one
      (@ncat_carrier (cat_succ cat_zero) X));

assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  h
  : τ (IsObjTruncCat (cat_dim_trunc_level n) C);

assertnot (P Q : τ OmegaEquivAlongEvidenceProp_D0)
  (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  @ncat_obj_trunc_from_evidence_prop P n C h
  ≡ @ncat_obj_trunc_from_evidence_prop Q n C h;

// A typed proof-time comparison also retains the capability input.
assertnot (P Q : τ OmegaEquivAlongEvidenceProp_D0)
  (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C)) ⊢
  @eq_refl
    (IsObjTruncCat (cat_dim_trunc_level n) C)
    (@ncat_obj_trunc_from_evidence_prop P n C h)
  : τ (@=
      (IsObjTruncCat (cat_dim_trunc_level n) C)
      (@ncat_obj_trunc_from_evidence_prop P n C h)
      (@ncat_obj_trunc_from_evidence_prop Q n C h));

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_path_view_refl_D0 C x y f u
  : τ (IsPropGrpd (@OmegaEquivAlong_D0 C x y f));
