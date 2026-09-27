/* Reviewer example: feasibility-first structured path-cubical operators. */

require open emdash.emdash3_2_path_cubical_structured_operators;

// A structured successor exposes its two newest-coordinate faces.
assert [S : τ PathCubeSpecU]
  (z : τ (@path_cube_spec_cube (@path_cube_spec_step S))) ⊢
  @path_structured_step_src S z
  : τ (@path_cube_spec_cube S);

assert [S : τ PathCubeSpecU]
  (z : τ (@path_cube_spec_cube (@path_cube_spec_step S))) ⊢
  @path_structured_step_tgt S z
  : τ (@path_cube_spec_cube S);

// Degeneracy is constant in the newest coordinate, so both faces compute.
assert [S : τ PathCubeSpecU]
  (c : τ (@path_cube_spec_cube S)) ⊢
  @path_structured_step_src
    S (@path_structured_step_degenerate S c)
  ≡ c;

assert [S : τ PathCubeSpecU]
  (c : τ (@path_cube_spec_cube S)) ⊢
  @path_structured_step_tgt
    S (@path_structured_step_degenerate S c)
  ≡ c;

// Its equality action remains an ordinary whole Path functor.
assert (S : τ PathCubeSpecU) ⊢
  @path_structured_step_degenerate_path_func S
  : τ (Functor
      (Path_cat (@path_cube_spec_cube S))
      (Path_cat (@path_cube_spec_cube (@path_cube_spec_step S))));

symbol review_structured_path_square
  [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b))
  : τ (@PathStructuredSquare_grpd A)
≔ @path_structured_square_intro
    A
    (@path_square_boundary_intro A x00 x01 x10 x11 u v a b)
    alpha;

// Fixed coordinate exchange swaps the vertices and four edge roles.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_square_boundary_x01
    A
    (@path_structured_square_boundary
      A
      (@path_structured_square_transpose
        A (@review_structured_path_square
          A x00 x01 x10 x11 u v a b alpha)))
  ≡ x10;

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_square_boundary_u
    A
    (@path_structured_square_boundary
      A
      (@path_structured_square_transpose
        A (@review_structured_path_square
          A x00 x01 x10 x11 u v a b alpha)))
  ≡ a;

// The transposed filler is exactly the reversed original equality.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_structured_square_filler
    A
    (@path_structured_square_transpose
      A (@review_structured_path_square
        A x00 x01 x10 x11 u v a b alpha))
  ≡ @eq_sym
      (@= A x00 x11)
      (@comp_fapp0 (Path_cat A) x00 x01 x11 b u)
      (@comp_fapp0 (Path_cat A) x00 x10 x11 v a)
      alpha;

// Transposition also retains ordinary equality action and native realization.
assert (A : Grpd) ⊢
  @path_structured_square_transpose_path_func A
  : τ (Functor
      (Path_cat (@PathStructuredSquare_grpd A))
      (Path_cat (@PathStructuredSquare_grpd A)));

assert [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A)) ⊢
  @path_structured_square_to_native
    A (@path_structured_square_transpose A S)
  : τ (@PathCube_grpd A (succ (succ zero)));

// The already-active structured fill remains an arbitrary-dimensional
// algebraic section; this file introduces no second filler.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (box : τ (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))) ⊢
  @path_structured_open_box_new_left_section
    (@path_cube_spec A n) box
  : τ (@=
      (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))
      (@path_structured_open_box_new_left_restrict
        (@path_cube_spec A n)
        (@path_structured_open_box_new_left_fill
          (@path_cube_spec A n) box))
      box);

assert [A : Grpd]
  (n : τ Nat_grpd)
  (box : τ (@StructuredOpenBoxNewLeft_grpd (@path_cube_spec A n))) ⊢
  @path_structured_open_box_new_left_native_fill A n box
  : τ (@PathCube_grpd A (succ n));

// Degenerate structured cubes also realize one-way into the native tower.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (c : τ (@StructuredPathCubeRec_grpd A n)) ⊢
  (@path_structured_path_cube_realize_function A (succ n))
    (@path_structured_step_degenerate (@path_cube_spec A n) c)
  : τ (@PathCube_grpd A (succ n));

type @path_structured_step_src;
type @path_structured_step_degenerate;
type @path_structured_square_transpose;
type @path_structured_open_box_new_left_section;
