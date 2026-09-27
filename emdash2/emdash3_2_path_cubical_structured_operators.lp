/*
  Emdash v3.2: feasibility-first structured path-cubical operators.

  A structured successor cube already stores two predecessor cubes, equality
  of their boundaries, and a PathOver between their fillers.  Its two newest
  faces are therefore ordinary Sigma projections.  Reflexivity constructs a
  cube constant in the newest coordinate, and both face observations compute
  back to the original cube.

  At dimension two, exchanging the two coordinates swaps u/a and v/b.  The
  filler orientation reverses from `b o u = v o a` to `v o a = b o u`, so
  ordinary equality symmetry constructs the transposed square.  This is a
  fixed feasibility witness, not a generic Cartesian substitution calculus.

  All operations are transparent and rule-free.  Existing structured
  new-left filling, its section, and one-way native realization remain their
  own owners.
*/

require open emdash.emdash3_2_path_cubical_structured_native_low_dimensions;

// Newest-coordinate source and target faces of one structured successor.
symbol path_structured_step_src
  [S : τ PathCubeSpecU]
  (z : τ (@path_cube_spec_cube (@path_cube_spec_step S)))
  : τ (@path_cube_spec_cube S)
≔ sigma_Fst (sigma_Fst z);

symbol path_structured_step_tgt
  [S : τ PathCubeSpecU]
  (z : τ (@path_cube_spec_cube (@path_cube_spec_step S)))
  : τ (@path_cube_spec_cube S)
≔ sigma_Fst (sigma_Snd (sigma_Fst z));

symbol path_structured_step_src_function
  (S : τ PathCubeSpecU)
  : τ (@Function_grpd
      (@path_cube_spec_cube (@path_cube_spec_step S))
      (@path_cube_spec_cube S))
≔ λ z : τ (@path_cube_spec_cube (@path_cube_spec_step S)),
    @path_structured_step_src S z;

symbol path_structured_step_tgt_function
  (S : τ PathCubeSpecU)
  : τ (@Function_grpd
      (@path_cube_spec_cube (@path_cube_spec_step S))
      (@path_cube_spec_cube S))
≔ λ z : τ (@path_cube_spec_cube (@path_cube_spec_step S)),
    @path_structured_step_tgt S z;

// Degeneracy constant in the newest coordinate.
symbol path_structured_step_degenerate
  [S : τ PathCubeSpecU]
  (c : τ (@path_cube_spec_cube S))
  : τ (@path_cube_spec_cube (@path_cube_spec_step S))
≔ @path_cube_spec_step_cube_intro
    S
    c c
    (@eq_refl (@path_cube_spec_boundary S) (sigma_Fst c))
    (@pathover_refl
      (@path_cube_spec_boundary S)
      (λ b : τ (@path_cube_spec_boundary S), @path_cube_spec_rel S b)
      (sigma_Fst c)
      (sigma_Snd c));

symbol path_structured_step_degenerate_function
  (S : τ PathCubeSpecU)
  : τ (@Function_grpd
      (@path_cube_spec_cube S)
      (@path_cube_spec_cube (@path_cube_spec_step S)))
≔ λ c : τ (@path_cube_spec_cube S),
    @path_structured_step_degenerate S c;

// Equality action of structured degeneracy remains available at every level.
symbol path_structured_step_degenerate_path_func
  (S : τ PathCubeSpecU)
  : τ (Functor
      (Path_cat (@path_cube_spec_cube S))
      (Path_cat (@path_cube_spec_cube (@path_cube_spec_step S))))
≔ @path_map_func
    (@path_cube_spec_cube S)
    (@path_cube_spec_cube (@path_cube_spec_step S))
    (@path_structured_step_degenerate_function S);

// Boundary of the fixed dimension-two coordinate transpose.
symbol path_structured_square_transpose_boundary
  [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A))
  : τ (@PathSquareBoundary_grpd A)
≔ @path_square_boundary_intro
    A
    (path_square_boundary_x00 (path_structured_square_boundary S))
    (path_square_boundary_x10 (path_structured_square_boundary S))
    (path_square_boundary_x01 (path_structured_square_boundary S))
    (path_square_boundary_x11 (path_structured_square_boundary S))
    (path_square_boundary_a (path_structured_square_boundary S))
    (path_square_boundary_b (path_structured_square_boundary S))
    (path_square_boundary_u (path_structured_square_boundary S))
    (path_square_boundary_v (path_structured_square_boundary S));

// Coordinate exchange reverses the selected square equality.
symbol path_structured_square_transpose_filler
  [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A))
  : τ (@PathSquareRel_grpd
      A (@path_structured_square_transpose_boundary A S))
≔ @eq_sym
    (@= A
      (path_square_boundary_x00 (path_structured_square_boundary S))
      (path_square_boundary_x11 (path_structured_square_boundary S)))
    (@comp_fapp0
      (Path_cat A)
      (path_square_boundary_x00 (path_structured_square_boundary S))
      (path_square_boundary_x01 (path_structured_square_boundary S))
      (path_square_boundary_x11 (path_structured_square_boundary S))
      (path_square_boundary_b (path_structured_square_boundary S))
      (path_square_boundary_u (path_structured_square_boundary S)))
    (@comp_fapp0
      (Path_cat A)
      (path_square_boundary_x00 (path_structured_square_boundary S))
      (path_square_boundary_x10 (path_structured_square_boundary S))
      (path_square_boundary_x11 (path_structured_square_boundary S))
      (path_square_boundary_v (path_structured_square_boundary S))
      (path_square_boundary_a (path_structured_square_boundary S)))
    (path_structured_square_filler S);

symbol path_structured_square_transpose
  [A : Grpd]
  (S : τ (@PathStructuredSquare_grpd A))
  : τ (@PathStructuredSquare_grpd A)
≔ @path_structured_square_intro
    A
    (@path_structured_square_transpose_boundary A S)
    (@path_structured_square_transpose_filler A S);

symbol path_structured_square_transpose_function
  (A : Grpd)
  : τ (@Function_grpd
      (@PathStructuredSquare_grpd A)
      (@PathStructuredSquare_grpd A))
≔ λ S : τ (@PathStructuredSquare_grpd A),
    @path_structured_square_transpose A S;

// Equality action of fixed square transposition is inherited from Path_map.
symbol path_structured_square_transpose_path_func
  (A : Grpd)
  : τ (Functor
      (Path_cat (@PathStructuredSquare_grpd A))
      (Path_cat (@PathStructuredSquare_grpd A)))
≔ @path_map_func
    (@PathStructuredSquare_grpd A)
    (@PathStructuredSquare_grpd A)
    (@path_structured_square_transpose_function A);
