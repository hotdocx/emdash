/*
  Emdash v3.2: one compatible five-face box and native dimension-three fill.

  A square boundary is the completed missing-b frame plus its fourth edge. A
  structured square is a boundary plus the existing filler `b o u = v o a`.
  The selected cube box missing its outer source stores two square boundaries,
  a path q between them (the four compatible side faces), and the target
  filler. Backward J transport along q supplies the missing source filler;
  reflexivity gives the dependent filler over q.

  `sigma_path_intro` turns that data into equality of structured squares.
  Mapping the equality to native square objects and applying the existing core
  inclusion produces a native cube. No `IsGroupoidalCat` or pseudo profile is
  assumed.
*/

require open emdash.emdash3_2_path_cubical_open_box_addresses;

// Four-edge boundary of a path square, grouped over the missing-b frame.
symbol PathSquareBoundary_grpd
  (A : Grpd)
  : Grpd
≔ `Σ_ frame : τ (@PathOpenSquareMissingB_grpd A),
    @path_square_b_grpd
      A
      (path_open_square_x00 frame)
      (path_open_square_x01 frame)
      (path_open_square_x10 frame)
      (path_open_square_x11 frame);

symbol path_square_boundary_intro
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  : τ (@PathSquareBoundary_grpd A)
≔ Struct_sigma
    (@path_open_square_missing_b_intro A x00 x01 x10 x11 u v a)
    b;

symbol path_square_boundary_frame [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@PathOpenSquareMissingB_grpd A)
≔ sigma_Fst B;

symbol path_square_boundary_x00 [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A)) : τ A
≔ path_open_square_x00 (path_square_boundary_frame B);

symbol path_square_boundary_x01 [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A)) : τ A
≔ path_open_square_x01 (path_square_boundary_frame B);

symbol path_square_boundary_x10 [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A)) : τ A
≔ path_open_square_x10 (path_square_boundary_frame B);

symbol path_square_boundary_x11 [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A)) : τ A
≔ path_open_square_x11 (path_square_boundary_frame B);

symbol path_square_boundary_u [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@= A (path_square_boundary_x00 B) (path_square_boundary_x01 B))
≔ @path_open_square_missing_b_u A (path_square_boundary_frame B);

symbol path_square_boundary_v [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@= A (path_square_boundary_x10 B) (path_square_boundary_x11 B))
≔ @path_open_square_missing_b_v A (path_square_boundary_frame B);

symbol path_square_boundary_a [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@= A (path_square_boundary_x00 B) (path_square_boundary_x10 B))
≔ @path_open_square_missing_b_a A (path_square_boundary_frame B);

symbol path_square_boundary_b [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@= A (path_square_boundary_x01 B) (path_square_boundary_x11 B))
≔ sigma_Snd B;

// Four boundary edges as native dimension-one path cubes.
symbol path_square_boundary_native_u [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@PathCube_grpd A (succ zero))
≔ @path_cube_edge
    A (path_square_boundary_x00 B) (path_square_boundary_x01 B)
    (path_square_boundary_u B);

symbol path_square_boundary_native_v [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@PathCube_grpd A (succ zero))
≔ @path_cube_edge
    A (path_square_boundary_x10 B) (path_square_boundary_x11 B)
    (path_square_boundary_v B);

symbol path_square_boundary_native_a [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@PathCube_grpd A (succ zero))
≔ @path_cube_edge
    A (path_square_boundary_x00 B) (path_square_boundary_x10 B)
    (path_square_boundary_a B);

symbol path_square_boundary_native_b [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : τ (@PathCube_grpd A (succ zero))
≔ @path_cube_edge
    A (path_square_boundary_x01 B) (path_square_boundary_x11 B)
    (path_square_boundary_b B);

// Filler family over a square boundary.
symbol PathSquareRel_grpd
  [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  : Grpd
≔ @PathSquareFiller_grpd
    A
    (path_square_boundary_x00 B)
    (path_square_boundary_x01 B)
    (path_square_boundary_x10 B)
    (path_square_boundary_x11 B)
    (path_square_boundary_u B)
    (path_square_boundary_v B)
    (path_square_boundary_a B)
    (path_square_boundary_b B);

// Structured square = boundary plus filler.
symbol PathStructuredSquare_grpd
  (A : Grpd)
  : Grpd
≔ `Σ_ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B;

symbol path_structured_square_intro
  [A : Grpd]
  (B : τ (@PathSquareBoundary_grpd A))
  (alpha : τ (@PathSquareRel_grpd A B))
  : τ (@PathStructuredSquare_grpd A)
≔ Struct_sigma B alpha;

symbol path_structured_square_boundary [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A))
  : τ (@PathSquareBoundary_grpd A)
≔ sigma_Fst S;

symbol path_structured_square_filler [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A))
  : τ (@PathSquareRel_grpd A (path_structured_square_boundary S))
≔ sigma_Snd S;

// Native dimension-two square represented by one structured square.
symbol path_structured_square_to_native
  [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_cube_square
    A
    (path_square_boundary_x00 (path_structured_square_boundary S))
    (path_square_boundary_x01 (path_structured_square_boundary S))
    (path_square_boundary_x10 (path_structured_square_boundary S))
    (path_square_boundary_x11 (path_structured_square_boundary S))
    (path_square_boundary_u (path_structured_square_boundary S))
    (path_square_boundary_v (path_structured_square_boundary S))
    (path_square_boundary_a (path_structured_square_boundary S))
    (path_square_boundary_b (path_structured_square_boundary S))
    (path_structured_square_filler S);

symbol path_structured_square_to_native_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathStructuredSquare_grpd A)
      (@PathCube_grpd A (succ (succ zero))))
≔ λ S : τ (@PathStructuredSquare_grpd A),
    @path_structured_square_to_native A S;

// Compatible five-face cube box missing the outer source square.
symbol PathCube3MissingSource_grpd
  (A : Grpd)
  : Grpd
≔ `Σ_ B0 : τ (@PathSquareBoundary_grpd A),
   `Σ_ B1 : τ (@PathSquareBoundary_grpd A),
   `Σ_ q : τ (@= (@PathSquareBoundary_grpd A) B0 B1),
      @PathSquareRel_grpd A B1;

symbol path_cube3_missing_source_intro
  [A : Grpd]
  (B0 B1 : τ (@PathSquareBoundary_grpd A))
  (q : τ (@= (@PathSquareBoundary_grpd A) B0 B1))
  (target : τ (@PathSquareRel_grpd A B1))
  : τ (@PathCube3MissingSource_grpd A)
≔ Struct_sigma B0 (Struct_sigma B1 (Struct_sigma q target));

symbol path_cube3_missing_source_B0 [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathSquareBoundary_grpd A)
≔ sigma_Fst box;

symbol path_cube3_missing_source_B1 [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathSquareBoundary_grpd A)
≔ sigma_Fst (sigma_Snd box);

symbol path_cube3_missing_source_q [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@= (@PathSquareBoundary_grpd A)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box))
≔ sigma_Fst (sigma_Snd (sigma_Snd box));

symbol path_cube3_missing_source_target [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathSquareRel_grpd A (path_cube3_missing_source_B1 box))
≔ sigma_Snd (sigma_Snd (sigma_Snd box));

// The four retained side faces encoded by q, realized as native squares.
symbol path_cube3_missing_source_side_u
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box)))
≔ @path_to_hom
    (@PathCubicalLevel_cat A (succ zero))
    (@path_square_boundary_native_u A (path_cube3_missing_source_B0 box))
    (@path_square_boundary_native_u A (path_cube3_missing_source_B1 box))
    (@eq_ap
      (@PathSquareBoundary_grpd A)
      (@PathCube_grpd A (succ zero))
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_u A B)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_q box));

symbol path_cube3_missing_source_side_v
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box)))
≔ @path_to_hom
    (@PathCubicalLevel_cat A (succ zero))
    (@path_square_boundary_native_v A (path_cube3_missing_source_B0 box))
    (@path_square_boundary_native_v A (path_cube3_missing_source_B1 box))
    (@eq_ap
      (@PathSquareBoundary_grpd A)
      (@PathCube_grpd A (succ zero))
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_v A B)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_q box));

symbol path_cube3_missing_source_side_a
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box)))
≔ @path_to_hom
    (@PathCubicalLevel_cat A (succ zero))
    (@path_square_boundary_native_a A (path_cube3_missing_source_B0 box))
    (@path_square_boundary_native_a A (path_cube3_missing_source_B1 box))
    (@eq_ap
      (@PathSquareBoundary_grpd A)
      (@PathCube_grpd A (succ zero))
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_a A B)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_q box));

symbol path_cube3_missing_source_side_b
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ zero))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
      (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box)))
≔ @path_to_hom
    (@PathCubicalLevel_cat A (succ zero))
    (@path_square_boundary_native_b A (path_cube3_missing_source_B0 box))
    (@path_square_boundary_native_b A (path_cube3_missing_source_B1 box))
    (@eq_ap
      (@PathSquareBoundary_grpd A)
      (@PathCube_grpd A (succ zero))
      (λ B : τ (@PathSquareBoundary_grpd A),
        @path_square_boundary_native_b A B)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_q box));

// Constructor-complete elimination of the selected five-face box.
injective symbol path_cube3_missing_source_ind
  [A : Grpd]
  (Q : τ (@PathCube3MissingSource_grpd A) → Grpd)
  (c : Π B0 : τ (@PathSquareBoundary_grpd A),
       Π B1 : τ (@PathSquareBoundary_grpd A),
       Π q : τ (@= (@PathSquareBoundary_grpd A) B0 B1),
       Π target : τ (@PathSquareRel_grpd A B1),
       τ (Q (@path_cube3_missing_source_intro A B0 B1 q target)))
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Q box);

rule @path_cube3_missing_source_ind
      _ _ $c
      (Struct_sigma $B0 (Struct_sigma $B1 (Struct_sigma $q $target)))
  ↪ $c $B0 $B1 $q $target;

// Selected missing source filler by backward J transport.
symbol path_cube3_missing_source_hcomp
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathSquareRel_grpd A (path_cube3_missing_source_B0 box))
≔ @ind_eq
    (@PathSquareBoundary_grpd A)
    (path_cube3_missing_source_B0 box)
    (path_cube3_missing_source_B1 box)
    (path_cube3_missing_source_q box)
    (λ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B)
    (path_cube3_missing_source_target box);

// Dependent filler over the four compatible side faces q.
symbol path_cube3_missing_source_pathover
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathOver
      (@PathSquareBoundary_grpd A)
      (λ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B)
      (path_cube3_missing_source_B0 box)
      (path_cube3_missing_source_B1 box)
      (path_cube3_missing_source_q box)
      (path_cube3_missing_source_hcomp box)
      (path_cube3_missing_source_target box))
≔ @eq_refl
    (@PathSquareRel_grpd A (path_cube3_missing_source_B0 box))
    (path_cube3_missing_source_hcomp box);

// Full structured cube: two boundaries, their four-side path, both fillers,
// and the dependent top cell.
symbol PathStructuredCube3_grpd
  (A : Grpd)
  : Grpd
≔ `Σ_ B0 : τ (@PathSquareBoundary_grpd A),
   `Σ_ B1 : τ (@PathSquareBoundary_grpd A),
   `Σ_ q : τ (@= (@PathSquareBoundary_grpd A) B0 B1),
   `Σ_ source : τ (@PathSquareRel_grpd A B0),
   `Σ_ target : τ (@PathSquareRel_grpd A B1),
      @PathOver
        (@PathSquareBoundary_grpd A)
        (λ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B)
        B0 B1 q source target;

symbol path_structured_cube3_intro
  [A : Grpd]
  (B0 B1 : τ (@PathSquareBoundary_grpd A))
  (q : τ (@= (@PathSquareBoundary_grpd A) B0 B1))
  (source : τ (@PathSquareRel_grpd A B0))
  (target : τ (@PathSquareRel_grpd A B1))
  (top : τ (@PathOver
    (@PathSquareBoundary_grpd A)
    (λ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B)
    B0 B1 q source target))
  : τ (@PathStructuredCube3_grpd A)
≔ Struct_sigma B0
    (Struct_sigma B1
      (Struct_sigma q
        (Struct_sigma source
          (Struct_sigma target top))));

symbol path_cube3_missing_source_structured_fill
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathStructuredCube3_grpd A)
≔ @path_structured_cube3_intro
    A
    (path_cube3_missing_source_B0 box)
    (path_cube3_missing_source_B1 box)
    (path_cube3_missing_source_q box)
    (path_cube3_missing_source_hcomp box)
    (path_cube3_missing_source_target box)
    (path_cube3_missing_source_pathover box);

// Restriction drops the selected source filler and top cell.
symbol path_structured_cube3_restrict_missing_source
  [A : Grpd]
  (cube : τ (@PathStructuredCube3_grpd A))
  : τ (@PathCube3MissingSource_grpd A)
≔ @path_cube3_missing_source_intro
    A
    (sigma_Fst cube)
    (sigma_Fst (sigma_Snd cube))
    (sigma_Fst (sigma_Snd (sigma_Snd cube)))
    (sigma_Fst (sigma_Snd
      (sigma_Snd (sigma_Snd (sigma_Snd cube)))));

// The groupoidal structured fill is an algebraic section.
symbol path_cube3_missing_source_structured_section
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@=
      (@PathCube3MissingSource_grpd A)
      (@path_structured_cube3_restrict_missing_source
        A (@path_cube3_missing_source_structured_fill A box))
      box)
≔ @path_cube3_missing_source_ind
    A
    (λ box0 : τ (@PathCube3MissingSource_grpd A),
      @=
        (@PathCube3MissingSource_grpd A)
        (@path_structured_cube3_restrict_missing_source
          A (@path_cube3_missing_source_structured_fill A box0))
        box0)
    (λ B0 : τ (@PathSquareBoundary_grpd A),
      λ B1 : τ (@PathSquareBoundary_grpd A),
        λ q : τ (@= (@PathSquareBoundary_grpd A) B0 B1),
          λ target : τ (@PathSquareRel_grpd A B1),
            @eq_refl
              (@PathCube3MissingSource_grpd A)
              (@path_cube3_missing_source_intro A B0 B1 q target))
    box;

// Source/target structured squares and their equality.
symbol path_cube3_missing_source_structured_source
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathStructuredSquare_grpd A)
≔ @path_structured_square_intro
    A
    (path_cube3_missing_source_B0 box)
    (path_cube3_missing_source_hcomp box);

symbol path_cube3_missing_source_structured_target
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathStructuredSquare_grpd A)
≔ @path_structured_square_intro
    A
    (path_cube3_missing_source_B1 box)
    (path_cube3_missing_source_target box);

symbol path_cube3_missing_source_structured_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@= (@PathStructuredSquare_grpd A)
      (path_cube3_missing_source_structured_source box)
      (path_cube3_missing_source_structured_target box))
≔ @sigma_path_intro
    (@PathSquareBoundary_grpd A)
    (λ B : τ (@PathSquareBoundary_grpd A), @PathSquareRel_grpd A B)
    (path_cube3_missing_source_B0 box)
    (path_cube3_missing_source_B1 box)
    (path_cube3_missing_source_hcomp box)
    (path_cube3_missing_source_target box)
    (path_cube3_missing_source_q box)
    (path_cube3_missing_source_pathover box);

// Equality of the corresponding native square objects.
symbol path_cube3_missing_source_native_path
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@= (@PathCube_grpd A (succ (succ zero)))
      (@path_structured_square_to_native
        A (path_cube3_missing_source_structured_source box))
      (@path_structured_square_to_native
        A (path_cube3_missing_source_structured_target box)))
≔ @eq_ap
    (@PathStructuredSquare_grpd A)
    (@PathCube_grpd A (succ (succ zero)))
    (@path_structured_square_to_native_function A)
    (path_cube3_missing_source_structured_source box)
    (path_cube3_missing_source_structured_target box)
    (path_cube3_missing_source_structured_path box);

// Core inclusion realizes that equality as a native Level-2 arrow.
symbol path_cube3_missing_source_native_arrow
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (Hom
      (@PathCubicalLevel_cat A (succ (succ zero)))
      (@path_structured_square_to_native
        A (path_cube3_missing_source_structured_source box))
      (@path_structured_square_to_native
        A (path_cube3_missing_source_structured_target box)))
≔ @path_to_hom
    (@PathCubicalLevel_cat A (succ (succ zero)))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box))
    (@path_cube3_missing_source_native_path A box);

// Native dimension-three cube selected by the compatible five-face box.
symbol path_cube3_fill_missing_source
  [A : Grpd]
  (box : τ (@PathCube3MissingSource_grpd A))
  : τ (@PathCube_grpd A (succ (succ (succ zero))))
≔ @path_cube_succ
    A (succ (succ zero))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_source box))
    (@path_structured_square_to_native
      A (path_cube3_missing_source_structured_target box))
    (@path_cube3_missing_source_native_arrow A box);

// The first next action of native realization remains the core hom action.
symbol path_cube3_native_realization_hom_func
  [A : Grpd]
  [S T : τ (@PathCube_grpd A (succ (succ zero)))]
  : τ (Functor
      (Path_cat (@= (@PathCube_grpd A (succ (succ zero))) S T))
      (Hom_cat (@PathCubicalLevel_cat A (succ (succ zero))) S T))
≔ @core_incl_hom_func (@PathCubicalLevel_cat A (succ (succ zero))) S T;
