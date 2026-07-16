/*
  Reviewer milestone: D1 public fixed-map omega-equivalence and decoder.

  A public omega-equivalence is a selected arrow paired with fixed-arrow
  evidence. Opposite and Product closure are evidence-owned, the canonical
  categorical decoder supplies propositional round trips, and D0b turns a
  category path into an iterable next-hom omega-equivalence. Package eta,
  reverse fibre eta, and the open decoder/path-to-hom squares remain absent.
*/

require open emdash.emdash3_2;

assert [C : Cat]
  [x y : τ (Obj C)] ⊢
  OmegaEquiv C x y
  ≡ `Σ_ f : τ (Hom C x y), @OmegaEquivAlong C x y f;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_to C x y (@omega_equiv_from_along C x y f u)
  ≡ f;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_evidence C x y (@omega_equiv_from_along C x y f u)
  ≡ u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong C x y f)) ⊢
  @omega_equiv_along_fibre_retract C x y f u
  ≡ eq_refl u;

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_path (Op_cat C) y x (@omega_equiv_op C x y e)
  ≡ @path_sym (Obj C) x y (@omega_equiv_path C x y e);

assert [A B : Cat]
  [x0 x1 : τ (Obj A)]
  [y0 y1 : τ (Obj B)]
  (eA : τ (OmegaEquiv A x0 x1))
  (eB : τ (OmegaEquiv B y0 y1)) ⊢
  sigma_Fst
    (@omega_equiv_path
      (Product_cat A B)
      (Struct_sigma x0 y0)
      (Struct_sigma x1 y1)
      (@omega_equiv_product A B x0 x1 y0 y1 eA eB))
  ≡ @omega_equiv_path A x0 x1 eA;

assert [C : Cat] ⊢
  @cat_univalence_from_decoder C
  : τ (CatUnivalence C);

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @omega_equiv_path_idtoequiv_cat C x y p
  : τ (@omega_equiv_path C x y (@idtoequiv_cat C x y p) = p);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @idtoequiv_cat_omega_equiv_path C x y e
  : τ (@idtoequiv_cat C x y (@omega_equiv_path C x y e) = e);

assert [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @cat_univalence_selected_path C x y e
  ≡ @omega_equiv_path C x y e;

assert [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @idtoequiv_cat_path_to_hom C x y p
  : τ (
      @omega_equiv_to C x y (@idtoequiv_cat C x y p)
      = @path_to_hom C x y p);

assert [A B : Cat]
  (p : τ (@= (Obj Cat_cat) A B))
  (x y : τ (Obj A)) ⊢
  @omega_equiv_evidence
    Cat_cat
    (Hom_cat A x y)
    (Hom_cat B
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) x)
      (@fapp0 A B (idtoequiv_cat_functor_D1 p) y))
    (@idtoequiv_cat_fapp1_D1 A B p x y)
  ≡ @idtoequiv_cat_fapp1_along_D1 A B p x y;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (e : τ (OmegaEquiv C x y)) ⊢
  @omega_equiv_from_along
    C x y
    (@omega_equiv_to C x y e)
    (@omega_equiv_evidence C x y e)
  ≡ e;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (h : τ (@OmegaEquivFibre C x y f)) ⊢
  @omega_equiv_along_to_fibre C x y f
    (@omega_equiv_fibre_to_along C x y f h)
  ≡ h;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @omega_equiv_path C x y (@idtoequiv_cat C x y p)
  ≡ p;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  (p : τ (x = y)) ⊢
  @omega_equiv_to C x y (@idtoequiv_cat C x y p)
  ≡ @path_to_hom C x y p;
