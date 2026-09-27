/*
  Emdash v3.2: inherited-face naturality of the selected native path cube.

  Functor action on an equality-induced arrow is first compared with equality
  action by the composite object function.  Equality action on a dependent
  pair introduced by `sigma_path_intro` then recovers action on its supplied
  base path.  Together these generic comparisons identify the four whole
  inherited faces of `path_cube3_fill_missing_source` with the four side
  squares already encoded by its boundary path q.

  Every result is a typed path between retained native face presentations.
  This module adds no face rewrite, endpoint collapse, opaque equation,
  groupoidality assumption, rule, or unifier.
*/

require open emdash.emdash3_2_path_cubical_cube3_open_box;
require open emdash.emdash3_2_eq1_hom_action;

// Equality action of a first-projection-dependent function on a Sigma path
// recovers equality action on the supplied base path.
symbol sigma_path_intro_base_ap
  [A B : Grpd]
  [P : τ A → Grpd]
  [x y : τ A]
  [a : τ (P x)]
  [b : τ (P y)]
  (p : τ (@= A x y))
  (q : τ (@PathOver A P x y p a b))
  (f : τ A → τ B)
  : τ (@=
      (@= B (f x) (f y))
      (@eq_ap
        (@Σ_ A P) B
        (λ z : @τΣ_ A P, f (sigma_Fst z))
        (@Struct_sigma A P x a)
        (@Struct_sigma A P y b)
        (@sigma_path_intro A P x y a b p q))
      (@eq_ap A B f x y p))
≔ @ind_eqr
    A y
    (λ x0 : τ A, λ p0 : τ (@= A x0 y),
      @Pi_grpd (P x0) (λ a0 : τ (P x0),
        @Pi_grpd (P y) (λ b0 : τ (P y),
          @Pi_grpd
            (@PathOver A P x0 y p0 a0 b0)
            (λ q0 : τ (@PathOver A P x0 y p0 a0 b0),
              @Pi_grpd
                (@Function_grpd A B)
                (λ f0 : τ A → τ B,
                  @=
                    (@= B (f0 x0) (f0 y))
                    (@eq_ap
                      (@Σ_ A P) B
                      (λ z : @τΣ_ A P, f0 (sigma_Fst z))
                      (@Struct_sigma A P x0 a0)
                      (@Struct_sigma A P y b0)
                      (@sigma_path_intro A P x0 y a0 b0 p0 q0))
                    (@eq_ap A B f0 x0 y p0))))))
    (λ a0 : τ (P y),
      λ b0 : τ (P y),
        λ q0 : τ (@PathOver A P y y (@eq_refl A y) a0 b0),
          λ f0 : τ A → τ B,
            (@ind_eqr
              (P y) b0
              (λ a1 : τ (P y), λ q1 : τ (@= (P y) a1 b0),
                @=
                  (@= B (f0 y) (f0 y))
                  (@eq_ap
                    (@Σ_ A P) B
                    (λ z : @τΣ_ A P, f0 (sigma_Fst z))
                    (@Struct_sigma A P y a1)
                    (@Struct_sigma A P y b0)
                    (@sigma_path_intro
                      A P y y a1 b0 (@eq_refl A y) q1))
                  (@eq_refl B (f0 y)))
              (@eq_refl
                (@= B (f0 y) (f0 y))
                (@eq_refl B (f0 y)))
              a0 q0))
    x p a b q f;

// Generic first stage: apply any whole Level-2 -> Level-1 face functor to the
// core-included path between the two realized structured squares.
symbol path_cube3_core_face_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  (F : τ (Functor
    (@PathCubicalLevel_cat A (succ (succ zero)))
    (@PathCubicalLevel_cat A (succ zero))))
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@fapp0
          (@PathCubicalLevel_cat A (succ (succ zero)))
          (@PathCubicalLevel_cat A (succ zero))
          F
          (@path_structured_square_to_native
            A (path_cube3_missing_source_structured_source box)))
        (@fapp0
          (@PathCubicalLevel_cat A (succ (succ zero)))
          (@PathCubicalLevel_cat A (succ zero))
          F
          (@path_structured_square_to_native
            A (path_cube3_missing_source_structured_target box))))
      (@fapp1_fapp0
        (@PathCubicalLevel_cat A (succ (succ zero)))
        (@PathCubicalLevel_cat A (succ zero))
        F
        (@path_structured_square_to_native
          A (path_cube3_missing_source_structured_source box))
        (@path_structured_square_to_native
          A (path_cube3_missing_source_structured_target box))
        (@path_cube3_missing_source_native_arrow A box))
      (@path_to_hom
        (@PathCubicalLevel_cat A (succ zero))
        (@fapp0
          (@PathCubicalLevel_cat A (succ (succ zero)))
          (@PathCubicalLevel_cat A (succ zero))
          F
          (@path_structured_square_to_native
            A (path_cube3_missing_source_structured_source box)))
        (@fapp0
          (@PathCubicalLevel_cat A (succ (succ zero)))
          (@PathCubicalLevel_cat A (succ zero))
          F
          (@path_structured_square_to_native
            A (path_cube3_missing_source_structured_target box)))
        (@eq_ap
          (@PathStructuredSquare_grpd A)
          (@PathCube_grpd A (succ zero))
          (λ S : τ (@PathStructuredSquare_grpd A),
            @fapp0
              (@PathCubicalLevel_cat A (succ (succ zero)))
              (@PathCubicalLevel_cat A (succ zero))
              F
              (@path_structured_square_to_native A S))
          (path_cube3_missing_source_structured_source box)
          (path_cube3_missing_source_structured_target box)
          (path_cube3_missing_source_structured_path box))))
≔ @path_to_hom_fapp1_eq_ap_comp
    (@PathStructuredSquare_grpd A)
    (@PathCubicalLevel_cat A (succ (succ zero)))
    (@PathCubicalLevel_cat A (succ zero))
    (@path_structured_square_to_native_function A)
    F
    (path_cube3_missing_source_structured_source box)
    (path_cube3_missing_source_structured_target box)
    (path_cube3_missing_source_structured_path box);

// Generic second stage: projecting a structured-square path to any boundary
// observation agrees with applying that observation directly to q.
symbol path_cube3_sigma_side_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  (f : τ (@PathSquareBoundary_grpd A)
    → τ (@PathCube_grpd A (succ zero)))
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (f (path_cube3_missing_source_B0 box))
        (f (path_cube3_missing_source_B1 box)))
      (@path_to_hom
        (@PathCubicalLevel_cat A (succ zero))
        (f (path_cube3_missing_source_B0 box))
        (f (path_cube3_missing_source_B1 box))
        (@eq_ap
          (@PathStructuredSquare_grpd A)
          (@PathCube_grpd A (succ zero))
          (λ S : τ (@PathStructuredSquare_grpd A),
            f (path_structured_square_boundary S))
          (path_cube3_missing_source_structured_source box)
          (path_cube3_missing_source_structured_target box)
          (path_cube3_missing_source_structured_path box)))
      (@path_to_hom
        (@PathCubicalLevel_cat A (succ zero))
        (f (path_cube3_missing_source_B0 box))
        (f (path_cube3_missing_source_B1 box))
        (@eq_ap
          (@PathSquareBoundary_grpd A)
          (@PathCube_grpd A (succ zero))
          f
          (path_cube3_missing_source_B0 box)
          (path_cube3_missing_source_B1 box)
          (path_cube3_missing_source_q box))))
≔ @path_to_hom_cong
    (@PathCubicalLevel_cat A (succ zero))
    (f (path_cube3_missing_source_B0 box))
    (f (path_cube3_missing_source_B1 box))
    (@eq_ap
      (@PathStructuredSquare_grpd A)
      (@PathCube_grpd A (succ zero))
      (λ S : τ (@PathStructuredSquare_grpd A),
        f (path_structured_square_boundary S))
      (path_cube3_missing_source_structured_source box)
      (path_cube3_missing_source_structured_target box)
      (path_cube3_missing_source_structured_path box))
    (@eq_ap
      (@PathSquareBoundary_grpd A)
      (@PathCube_grpd A (succ zero))
      f
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_q box))
    (@sigma_path_intro_base_ap
      (@PathSquareBoundary_grpd A)
      (@PathCube_grpd A (succ zero))
      (λ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_hcomp box)
      (path_cube3_missing_source_target box)
      (path_cube3_missing_source_q box)
      (path_cube3_missing_source_pathover box)
      f);

// The four generic inherited side faces, with their exact boundary endpoints.
symbol path_cube3_fill_outer_src
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
≔ @cubical_cube_outer_src
    (Path_cat A)
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box))
    (@path_cube3_missing_source_native_arrow A box);

symbol path_cube3_fill_outer_tgt
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box)))
≔ @cubical_cube_outer_tgt
    (Path_cat A)
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box))
    (@path_cube3_missing_source_native_arrow A box);

symbol path_cube3_fill_inner_src
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box)))
≔ @cubical_cube_inner_src
    (Path_cat A)
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box))
    (@path_cube3_missing_source_native_arrow A box);

symbol path_cube3_fill_inner_tgt
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box)))
≔ @cubical_cube_inner_tgt
    (Path_cat A)
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box))
    (@path_cube3_missing_source_native_arrow A box);

// Outer source = the u-side encoded by q.
symbol path_cube3_fill_outer_src_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_outer_src A box)
      (@path_cube3_missing_source_side_u A box))
≔ @eq_trans
    (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
    (@path_cube3_fill_outer_src A box)
    (@path_to_hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box))
      (@eq_ap
        (@PathStructuredSquare_grpd A)
        (@PathCube_grpd A (succ zero))
        (λ S : τ (@PathStructuredSquare_grpd A),
          @path_square_boundary_native_u
            A (path_structured_square_boundary S))
        (path_cube3_missing_source_structured_source box)
        (path_cube3_missing_source_structured_target box)
        (path_cube3_missing_source_structured_path box)))
    (@path_cube3_missing_source_side_u A box)
    (@path_cube3_core_face_path
      A box (@cubical_square_outer_src_func (Path_cat A)))
    (@path_cube3_sigma_side_path
      A box
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_u A B));

// Outer target = the v-side encoded by q.
symbol path_cube3_fill_outer_tgt_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_outer_tgt A box)
      (@path_cube3_missing_source_side_v A box))
≔ @eq_trans
    (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box)))
    (@path_cube3_fill_outer_tgt A box)
    (@path_to_hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box))
      (@eq_ap
        (@PathStructuredSquare_grpd A)
        (@PathCube_grpd A (succ zero))
        (λ S : τ (@PathStructuredSquare_grpd A),
          @path_square_boundary_native_v
            A (path_structured_square_boundary S))
        (path_cube3_missing_source_structured_source box)
        (path_cube3_missing_source_structured_target box)
        (path_cube3_missing_source_structured_path box)))
    (@path_cube3_missing_source_side_v A box)
    (@path_cube3_core_face_path
      A box (@cubical_square_outer_tgt_func (Path_cat A)))
    (@path_cube3_sigma_side_path
      A box
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_v A B));

// Inner source = the a-side encoded by q.
symbol path_cube3_fill_inner_src_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_inner_src A box)
      (@path_cube3_missing_source_side_a A box))
≔ @eq_trans
    (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box)))
    (@path_cube3_fill_inner_src A box)
    (@path_to_hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box))
      (@eq_ap
        (@PathStructuredSquare_grpd A)
        (@PathCube_grpd A (succ zero))
        (λ S : τ (@PathStructuredSquare_grpd A),
          @path_square_boundary_native_a
            A (path_structured_square_boundary S))
        (path_cube3_missing_source_structured_source box)
        (path_cube3_missing_source_structured_target box)
        (path_cube3_missing_source_structured_path box)))
    (@path_cube3_missing_source_side_a A box)
    (@path_cube3_core_face_path
      A box (@cubical_square_inner_src_func (Path_cat A)))
    (@path_cube3_sigma_side_path
      A box
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_a A B));

// Inner target = the b-side encoded by q.
symbol path_cube3_fill_inner_tgt_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@=
      (Hom
        (@PathCubicalLevel_cat A (succ zero))
        (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
        (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box)))
      (@path_cube3_fill_inner_tgt A box)
      (@path_cube3_missing_source_side_b A box))
≔ @eq_trans
    (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box)))
    (@path_cube3_fill_inner_tgt A box)
    (@path_to_hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box))
      (@eq_ap
        (@PathStructuredSquare_grpd A)
        (@PathCube_grpd A (succ zero))
        (λ S : τ (@PathStructuredSquare_grpd A),
          @path_square_boundary_native_b
            A (path_structured_square_boundary S))
        (path_cube3_missing_source_structured_source box)
        (path_cube3_missing_source_structured_target box)
        (path_cube3_missing_source_structured_path box)))
    (@path_cube3_missing_source_side_b A box)
    (@path_cube3_core_face_path
      A box (@cubical_square_inner_tgt_func (Path_cat A)))
    (@path_cube3_sigma_side_path
      A box
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_b A B));
