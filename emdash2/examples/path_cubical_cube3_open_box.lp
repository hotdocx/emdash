/* Reviewer example: compatible five-face groupoidal box and native cube fill. */

require open emdash.emdash3_2_path_cubical_cube3_open_box;

symbol review_path_cube3_boundary
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  : τ (@PathSquareBoundary_grpd A)
≔ @path_square_boundary_intro A x00 x01 x10 x11 u v a b;

symbol review_path_cube3_reflexive_box
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b))
  : τ (@PathCube3MissingSource_grpd A)
≔ @path_cube3_missing_source_intro
    A
    (@review_path_cube3_boundary A x00 x01 x10 x11 u v a b)
    (@review_path_cube3_boundary A x00 x01 x10 x11 u v a b)
    (@eq_refl
      (@PathSquareBoundary_grpd A)
      (@review_path_cube3_boundary A x00 x01 x10 x11 u v a b))
    alpha;

// Transport filling computes on a reflexive boundary path.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_cube3_missing_source_hcomp
    A (@review_path_cube3_reflexive_box
      A x00 x01 x10 x11 u v a b alpha)
  ≡ alpha;

// The structured filler is a section of the selected missing-source restriction.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_missing_source_structured_section A box
  : τ (@= (@PathCube3MissingSource_grpd A)
      (@path_structured_cube3_restrict_missing_source
        A (@path_cube3_missing_source_structured_fill A box))
      box);

// The equality q exposes four retained native side squares.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_missing_source_side_u A box
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)));

assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_missing_source_side_b A box
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box)));

// Core inclusion realizes the full structured equality as a native cube.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_fill_missing_source A box
  : τ (@PathCube_grpd A (succ (succ (succ zero))));

// New-coordinate source and target faces are the constructed/retained squares.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube_succ_src
    A (succ (succ zero)) (@path_cube3_fill_missing_source A box)
  ≡ @path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box);

assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube_succ_tgt
    A (succ (succ zero)) (@path_cube3_fill_missing_source A box)
  ≡ @path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box);

// The native cube arrow retains the existing core hom action.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube_succ_cell
    A (succ (succ zero)) (@path_cube3_fill_missing_source A box)
  ≡ @path_cube3_missing_source_native_arrow A box;

assert [A : Grpd]
  (S T : τ (@PathCube_grpd A (succ (succ zero)))) ⊢
  @path_cube3_native_realization_hom_func A S T
  : τ (Functor
      (Path_cat (@= (@PathCube_grpd A (succ (succ zero))) S T))
      (Hom_cat (@PathCubicalLevel_cat A (succ (succ zero))) S T));

type @PathCube3MissingSource_grpd;
type @path_cube3_missing_source_hcomp;
type @path_cube3_fill_missing_source;
