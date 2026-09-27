/* Reviewer example: all inherited faces of the selected native path cube. */

require open emdash.emdash3_2_path_cubical_face_naturality;

symbol review_face_naturality_boundary
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  : τ (@PathSquareBoundary_grpd A)
≔ @path_square_boundary_intro A x00 x01 x10 x11 u v a b;

symbol review_face_naturality_reflexive_box
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
    (@review_face_naturality_boundary A x00 x01 x10 x11 u v a b)
    (@review_face_naturality_boundary A x00 x01 x10 x11 u v a b)
    (@eq_refl
      (@PathSquareBoundary_grpd A)
      (@review_face_naturality_boundary A x00 x01 x10 x11 u v a b))
    alpha;

// The exact coordinate convention is outer-source/outer-target/inner-source/
// inner-target = u/v/a/b.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_fill_outer_src_path A box
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_outer_src A box)
      (@path_cube3_missing_source_side_u A box));

assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_fill_outer_tgt_path A box
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_outer_tgt A box)
      (@path_cube3_missing_source_side_v A box));

assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_fill_inner_src_path A box
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_inner_src A box)
      (@path_cube3_missing_source_side_a A box));

assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_cube3_fill_inner_tgt_path A box
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_inner_tgt A box)
      (@path_cube3_missing_source_side_b A box));

// The comparison is itself a path and can be included at the next native Hom.
assert [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A)) ⊢
  @path_to_hom
    (Hom_cat
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
    (@path_cube3_fill_outer_src A box)
    (@path_cube3_missing_source_side_u A box)
    (@path_cube3_fill_outer_src_path A box)
  : τ (Hom
      (Hom_cat
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_outer_src A box)
      (@path_cube3_missing_source_side_u A box));

// The fully reflexive constructor case reduces to reflexivity.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_cube3_fill_outer_src_path
    A
    (@review_face_naturality_reflexive_box
      A x00 x01 x10 x11 u v a b alpha)
  ≡ @eq_refl
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_u
          A (@review_face_naturality_boundary
            A x00 x01 x10 x11 u v a b))
        (@path_square_boundary_native_u
          A (@review_face_naturality_boundary
            A x00 x01 x10 x11 u v a b)))
      (@id
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_u
          A (@review_face_naturality_boundary
            A x00 x01 x10 x11 u v a b)));

type @sigma_path_intro_base_ap;
type @path_to_hom_fapp1_eq_ap_comp;
type @path_cube3_core_face_path;
type @path_cube3_fill_outer_src_path;
type @path_cube3_fill_outer_tgt_path;
type @path_cube3_fill_inner_src_path;
type @path_cube3_fill_inner_tgt_path;
