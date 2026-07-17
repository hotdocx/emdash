/*
  Reviewer milestone: finite observation paths for fixed-arrow evidence.

  The view packages exactly the selected left/right inverse arrows and the two
  recursive cell packages. It is intentionally one layer deep: public
  certificate equality remains opaque because the direct recursive rule does
  not satisfy the bounded normalization gate.
*/

require open emdash.emdash3_2;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)] ⊢
  @OmegaEquivAlongObservation_D0 C x y f
  : Grpd;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_observe_D0 C x y f u
  : τ (@OmegaEquivAlongObservation_D0 C x y f);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Fst (@omega_equiv_along_observe_D0 C x y f u)
  ≡ @omega_equiv_along_left_inv_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Fst (sigma_Snd (@omega_equiv_along_observe_D0 C x y f u))
  ≡ @omega_equiv_along_right_inv_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Fst
    (sigma_Snd
      (sigma_Snd (@omega_equiv_along_observe_D0 C x y f u)))
  ≡ @omega_equiv_along_left_cell_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  sigma_Snd
    (sigma_Snd
      (sigma_Snd (@omega_equiv_along_observe_D0 C x y f u)))
  ≡ @omega_equiv_along_right_cell_D0 C x y f u;

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_path_view_refl_D0 C x y f u
  : τ (@OmegaEquivAlongPathView_D0 C x y f u u);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  [u v : τ (@OmegaEquivAlong_D0 C x y f)]
  (p : τ (@= (@OmegaEquivAlong_D0 C x y f) u v)) ⊢
  @omega_equiv_along_path_view_encode_D0 C x y f u v p
  : τ (@OmegaEquivAlongPathView_D0 C x y f u v);

assert [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_path_view_encode_D0
    C x y f u u (@eq_refl (@OmegaEquivAlong_D0 C x y f) u)
  ≡ @omega_equiv_along_path_view_refl_D0 C x y f u;

assert [A B : Cat]
  [F : τ (Functor A B)]
  (u : τ (@OmegaEquivAlong_D0 Cat_cat A B F))
  (x y : τ (Obj A)) ⊢
  sigma_Fst
    (@omega_equiv_along_observe_D0
      Cat_cat
      (Hom_cat A x y)
      (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (@fapp1_func A B F x y)
      (@omega_equiv_along_fapp1_D0 A B F u x y))
  ≡ @omega_equiv_along_fapp1_left_inv_D0 A B F u x y;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u v : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @= (@OmegaEquivAlong_D0 C x y f) u v
  ≡ @OmegaEquivAlongPathView_D0 C x y f u v;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u : τ (@OmegaEquivAlong_D0 C x y f))
  (p : τ (@= (@OmegaEquivAlong_D0 C x y f) u u)) ⊢
  @omega_equiv_along_path_view_encode_D0 C x y f u u p
  ≡ @omega_equiv_along_path_view_refl_D0 C x y f u;

assertnot [C : Cat]
  [x y : τ (Obj C)]
  [f : τ (Hom C x y)]
  (u v : τ (@OmegaEquivAlong_D0 C x y f)) ⊢
  @omega_equiv_along_path_view_refl_D0 C x y f u
  : τ (@OmegaEquivAlongPathView_D0 C x y f u v);
