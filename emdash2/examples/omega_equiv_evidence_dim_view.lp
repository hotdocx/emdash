/*
  Reviewer milestone: dimension-indexed observation of fixed-arrow evidence.

  An explicit IsNCat witness bounds the observation tree. Dimension zero is
  Unit; each successor exposes the chosen inverse arrows and recursively
  observes both inverse cells one dimension lower. Opaque certificate equality
  remains distinct and the observation path interface is one-way.
*/

require open emdash.emdash3_2;

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @OmegaEquivAlongDimObservation_D0 n C h x y f
  : Grpd;

assert [C : Cat]
  (h : τ (IsNCat cat_zero C))
  [x y : τ (Obj C)]
  (f : τ (Hom C x y)) ⊢
  @OmegaEquivAlongDimObservation_D0 cat_zero C h x y f
  ≡ Unit_grpd;

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_dim_observe_D0 n C h x y f u
  : τ (@OmegaEquivAlongDimObservation_D0 n C h x y f);

assert [C : Cat]
  (h : τ (IsNCat cat_zero C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_dim_observe_D0 cat_zero C h x y f u
  ≡ tt;

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat (cat_succ n) C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Fst
    (@omega_equiv_along_dim_observe_D0
      (cat_succ n) C h x y f u)
  ≡ @omega_equiv_along_left_inv_D0 C x y f u;

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat (cat_succ n) C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Fst
    (sigma_Snd
      (@omega_equiv_along_dim_observe_D0
        (cat_succ n) C h x y f u))
  ≡ @omega_equiv_along_right_inv_D0 C x y f u;

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat (cat_succ n) C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Fst
    (sigma_Fst
      (sigma_Snd
        (sigma_Snd
          (@omega_equiv_along_dim_observe_D0
            (cat_succ n) C h x y f u))))
  ≡ @omega_equiv_to_D0
      (Hom_cat C x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f)
      (@id C x)
      (@omega_equiv_along_left_cell_D0 C x y f u);

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat (cat_succ n) C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Snd
    (sigma_Fst
      (sigma_Snd
        (sigma_Snd
          (@omega_equiv_along_dim_observe_D0
            (cat_succ n) C h x y f u))))
  ≡ @omega_equiv_along_dim_observe_D0
      n
      (Hom_cat C x x)
      (h x x)
      (@comp_fapp0 C x y x
        (@omega_equiv_along_left_inv_D0 C x y f u)
        f)
      (@id C x)
      (@omega_equiv_to_D0
        (Hom_cat C x x)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f)
        (@id C x)
        (@omega_equiv_along_left_cell_D0 C x y f u))
      (@omega_equiv_evidence_D0
        (Hom_cat C x x)
        (@comp_fapp0 C x y x
          (@omega_equiv_along_left_inv_D0 C x y f u)
          f)
        (@id C x)
        (@omega_equiv_along_left_cell_D0 C x y f u));

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_dim_path_view_refl_D0 n C h x y f u
  : τ (@OmegaEquivAlongDimPathView_D0 n C h x y f u u);

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  [u v : τ (@OmegaEquivAlong_D0 C x y f)]
  (p : τ (@= (@OmegaEquivAlong_D0 C x y f) u v)) ⊢
  @omega_equiv_along_dim_path_view_encode_D0 n C h x y f u v p
  : τ (@OmegaEquivAlongDimPathView_D0 n C h x y f u v);

assert (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_dim_path_view_encode_D0
    n C h x y f u u (@eq_refl (@OmegaEquivAlong_D0 C x y f) u)
  ≡ @omega_equiv_along_dim_path_view_refl_D0 n C h x y f u;

assert (X : τ OneCat)
  [x y : τ (Obj (@ncat_carrier (cat_succ cat_zero) X))]
  [f : τ (Hom (@ncat_carrier (cat_succ cat_zero) X) x y)]
  (u : τ (@OmegaEquivAlong_D0
      (@ncat_carrier (cat_succ cat_zero) X) x y f)) ⊢
  sigma_Snd
    (sigma_Fst
      (sigma_Snd
        (sigma_Snd
          (@omega_equiv_along_dim_observe_D0
            (cat_succ cat_zero)
            (@ncat_carrier (cat_succ cat_zero) X)
            (@ncat_evidence (cat_succ cat_zero) X)
            x y f u))))
  ≡ tt;

assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u v : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @= (@OmegaEquivAlong_D0 C x y f) u v
  ≡ @OmegaEquivAlongDimPathView_D0 n C h x y f u v;

assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u v : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @OmegaEquivAlongPathView_D0 C x y f u v
  ≡ @OmegaEquivAlongDimPathView_D0 n C h x y f u v;

assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  (p : τ (@= (@OmegaEquivAlong_D0 C x y f) u u)) ⊢
  @omega_equiv_along_dim_path_view_encode_D0 n C h x y f u u p
  ≡ @omega_equiv_along_dim_path_view_refl_D0 n C h x y f u;

// Typed proof-time control: there is no unification equation between distinct
// opaque-certificate observations at an open dimension.
assertnot (n : CatDim)
  [C : Cat]
  (h : τ (IsNCat n C))
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u v : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @eq_refl
    (@OmegaEquivAlongDimObservation_D0 n C h x y f)
    (@omega_equiv_along_dim_observe_D0 n C h x y f u)
  : τ (@=
      (@OmegaEquivAlongDimObservation_D0 n C h x y f)
      (@omega_equiv_along_dim_observe_D0 n C h x y f u)
      (@omega_equiv_along_dim_observe_D0 n C h x y f v));
