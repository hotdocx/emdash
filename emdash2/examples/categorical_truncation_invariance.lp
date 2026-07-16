/*
  Reviewer milestone: fixed-map omega-equivalence preserves object truncation
  by decoding a category path, mapping `Obj`, and reusing ordinary TypeEquiv
  truncation invariance.

  The induced object equivalence is decoder-owned; it is not asserted to
  expose the selected functor's object map by runtime conversion.
*/

require open emdash.emdash3_2;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @omega_equiv_along_obj_type_equiv A B F u
  : τ (TypeEquiv (Obj A) (Obj B));

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F)) ⊢
  @is_obj_trunc_cat_equiv_type_equiv n A B F u
  : τ (TypeEquiv (IsObjTruncCat n A) (IsObjTruncCat n B));

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to n A B F u h
  : τ (IsObjTruncCat n B);

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B)) ⊢
  @is_obj_trunc_cat_equiv_from n A B F u h
  : τ (IsObjTruncCat n A);

assert [A : Cat] ⊢
  @omega_equiv_along_obj_type_equiv
    A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A)
  ≡ @type_equiv_refl (Obj A);

assert (n : TruncLevel)
  [A : Cat]
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to
    n A A (@id_func A) (@omega_equiv_along_refl_D0 Cat_cat A) h
  ≡ h;

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n B)) ⊢
  type_equiv_right (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h
  : τ (
      @is_obj_trunc_cat_equiv_to n A B F u
        (@is_obj_trunc_cat_equiv_from n A B F u h)
      = h);

assert (n : TruncLevel)
  [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (h : τ (IsObjTruncCat n A)) ⊢
  type_equiv_left (@is_obj_trunc_cat_equiv_type_equiv n A B F u) h
  : τ (
      @is_obj_trunc_cat_equiv_from n A B F u
        (@is_obj_trunc_cat_equiv_to n A B F u h)
      = h);

assertnot [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong Cat_cat A B F))
  (x : τ (Obj A)) ⊢
  type_equiv_to (@omega_equiv_along_obj_type_equiv A B F u) x
  ≡ @fapp0 A B F x;

assertnot (n : TruncLevel)
  [A : Cat]
  [F : τ (Functor A A)]
  (u : τ (@OmegaEquivAlong Cat_cat A A F))
  (h : τ (IsObjTruncCat n A)) ⊢
  @is_obj_trunc_cat_equiv_to n A A F u h
  ≡ h;
