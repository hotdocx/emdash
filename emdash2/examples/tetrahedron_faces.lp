/*
  Focused reviewer for the four triangle cofaces of Delta[3].

  Every shared edge agrees by computing face-code composition. The three
  edges wholly inside the old Delta[2] also agree as composite realized
  functors. The three edges using the newly joined vertex deliberately remain
  distinct whole-functor presentations pending generic join-map composition.
*/

require open emdash.emdash3_2_tetrahedron_faces;

// The four cofaces use the expected join branches.
assert ⊢
  simplex_triangle_zero_one_two_func
  ≡ @join_fst_func
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat;

assert ⊢
  simplex_triangle_zero_one_three_func
  ≡ @join_map_func
      WalkingArrow_cat Terminal_cat
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat
      simplex_edge_zero_one_func
      (@strict_functor_carrier
        Terminal_cat Terminal_cat
        (@strict_identity_data Terminal_cat));

assert ⊢
  simplex_triangle_zero_two_three_func
  ≡ @join_map_func
      WalkingArrow_cat Terminal_cat
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat
      simplex_edge_zero_two_func
      (@strict_functor_carrier
        Terminal_cat Terminal_cat
        (@strict_identity_data Terminal_cat));

assert ⊢
  simplex_triangle_one_two_three_func
  ≡ @join_map_func
      WalkingArrow_cat Terminal_cat
      (@DirectedSimplex_cat (succ (succ zero))) Terminal_cat
      simplex_edge_one_two_func
      (@strict_functor_carrier
        Terminal_cat Terminal_cat
        (@strict_identity_data Terminal_cat));

// Shared edge 01: both code and whole realization compute.
assert ⊢
  @comp_fapp0 SemiDeltaPlus_cat
    (succ (succ zero)) (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    simplex_triangle_zero_one_two_code simplex_edge_zero_one_code
  ≡ @comp_fapp0 SemiDeltaPlus_cat
      (succ (succ zero)) (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_zero_one_three_code simplex_edge_zero_one_code;

assert ⊢
  @comp_fapp0 Cat_cat
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    (@DirectedSimplex_cat (succ (succ (succ zero))))
    simplex_triangle_zero_one_two_func simplex_edge_zero_one_func
  ≡ @comp_fapp0 Cat_cat
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      simplex_triangle_zero_one_three_func simplex_edge_zero_one_func;

// Shared edge 02.
assert ⊢
  @comp_fapp0 SemiDeltaPlus_cat
    (succ (succ zero)) (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    simplex_triangle_zero_one_two_code simplex_edge_zero_two_code
  ≡ @comp_fapp0 SemiDeltaPlus_cat
      (succ (succ zero)) (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_zero_two_three_code simplex_edge_zero_one_code;

assert ⊢
  @comp_fapp0 Cat_cat
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    (@DirectedSimplex_cat (succ (succ (succ zero))))
    simplex_triangle_zero_one_two_func simplex_edge_zero_two_func
  ≡ @comp_fapp0 Cat_cat
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      simplex_triangle_zero_two_three_func simplex_edge_zero_one_func;

// Shared edge 12.
assert ⊢
  @comp_fapp0 SemiDeltaPlus_cat
    (succ (succ zero)) (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    simplex_triangle_zero_one_two_code simplex_edge_one_two_code
  ≡ @comp_fapp0 SemiDeltaPlus_cat
      (succ (succ zero)) (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_one_two_three_code simplex_edge_zero_one_code;

assert ⊢
  @comp_fapp0 Cat_cat
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    (@DirectedSimplex_cat (succ (succ (succ zero))))
    simplex_triangle_zero_one_two_func simplex_edge_one_two_func
  ≡ @comp_fapp0 Cat_cat
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      simplex_triangle_one_two_three_func simplex_edge_zero_one_func;

// Shared edge 03 computes as one FaceCode, but not yet as one whole functor.
assert ⊢
  @comp_fapp0 SemiDeltaPlus_cat
    (succ (succ zero)) (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    simplex_triangle_zero_one_three_code simplex_edge_zero_two_code
  ≡ @comp_fapp0 SemiDeltaPlus_cat
      (succ (succ zero)) (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_zero_two_three_code simplex_edge_zero_two_code;

assertnot ⊢
  @comp_fapp0 Cat_cat
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    (@DirectedSimplex_cat (succ (succ (succ zero))))
    simplex_triangle_zero_one_three_func simplex_edge_zero_two_func
  ≡ @comp_fapp0 Cat_cat
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      simplex_triangle_zero_two_three_func simplex_edge_zero_two_func;

// Shared edge 13 has the same exact boundary.
assert ⊢
  @comp_fapp0 SemiDeltaPlus_cat
    (succ (succ zero)) (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    simplex_triangle_zero_one_three_code simplex_edge_one_two_code
  ≡ @comp_fapp0 SemiDeltaPlus_cat
      (succ (succ zero)) (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_one_two_three_code simplex_edge_zero_two_code;

assertnot ⊢
  @comp_fapp0 Cat_cat
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    (@DirectedSimplex_cat (succ (succ (succ zero))))
    simplex_triangle_zero_one_three_func simplex_edge_one_two_func
  ≡ @comp_fapp0 Cat_cat
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      simplex_triangle_one_two_three_func simplex_edge_zero_two_func;

// Shared edge 23 has the same exact boundary.
assert ⊢
  @comp_fapp0 SemiDeltaPlus_cat
    (succ (succ zero)) (succ (succ (succ zero)))
    (succ (succ (succ (succ zero))))
    simplex_triangle_zero_two_three_code simplex_edge_one_two_code
  ≡ @comp_fapp0 SemiDeltaPlus_cat
      (succ (succ zero)) (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_one_two_three_code simplex_edge_one_two_code;

assertnot ⊢
  @comp_fapp0 Cat_cat
    (@DirectedSimplex_cat (succ zero))
    (@DirectedSimplex_cat (succ (succ zero)))
    (@DirectedSimplex_cat (succ (succ (succ zero))))
    simplex_triangle_zero_two_three_func simplex_edge_one_two_func
  ≡ @comp_fapp0 Cat_cat
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      simplex_triangle_one_two_three_func simplex_edge_one_two_func;
