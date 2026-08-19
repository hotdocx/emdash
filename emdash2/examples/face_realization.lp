/*
  Reviewer for variable-dimension nonempty face realization.

  Raw and public skip/keep constructors compute through join recursion. The
  reviewer also records the exact remaining functoriality boundary: the edge
  identity is join_map(id,id), and the first new-vertex composite does not yet
  agree definitionally with composition of realized faces.
*/

require open emdash.emdash3_2_face_realization;
require open emdash.emdash3_2_tetrahedron_faces;

// Raw realization computes the two vertices of the directed edge.
assert ⊢
  @raw_face_realize_func zero (succ zero)
    (@raw_face_skip
      (succ zero) (succ zero)
      (@raw_face_keep zero zero raw_face_nil))
  ≡ @join_fst_func Terminal_cat Terminal_cat;

assert ⊢
  @raw_face_realize_func zero (succ zero)
    (@raw_face_keep
      zero (succ zero)
      (@raw_face_skip zero zero raw_face_nil))
  ≡ @join_snd_func Terminal_cat Terminal_cat;

// Recursive keep realizes the two non-old-base edges of the triangle.
assert ⊢
  @raw_face_realize_func (succ zero) (succ (succ zero))
    (@raw_face_keep
      (succ zero) (succ (succ zero))
      (@raw_face_skip
        (succ zero) (succ zero)
        (@raw_face_keep zero zero raw_face_nil)))
  ≡ @join_map_func
      Terminal_cat Terminal_cat WalkingArrow_cat Terminal_cat
      (@join_fst_func Terminal_cat Terminal_cat)
      (@id_func Terminal_cat);

assert ⊢
  @raw_face_realize_func (succ zero) (succ (succ zero))
    (@raw_face_keep
      (succ zero) (succ (succ zero))
      (@raw_face_keep
        zero (succ zero)
        (@raw_face_skip zero zero raw_face_nil)))
  ≡ @join_map_func
      Terminal_cat Terminal_cat WalkingArrow_cat Terminal_cat
      (@join_snd_func Terminal_cat Terminal_cat)
      (@id_func Terminal_cat);

// Public set-truncated constructors preserve the same computations.
assert ⊢
  @face_realize_func zero (succ zero)
    (@face_skip
      (succ zero) (succ zero)
      (@face_keep zero zero face_nil))
  ≡ @join_fst_func Terminal_cat Terminal_cat;

assert ⊢
  @face_realize_func zero (succ zero)
    (@face_keep
      zero (succ zero)
      (@face_skip zero zero face_nil))
  ≡ @join_snd_func Terminal_cat Terminal_cat;

// The point identity computes. At the next dimension, recursive realization
// deliberately retains join_map(id,id) instead of adding a local identity fold.
assert ⊢
  @face_realize_func zero zero (@face_identity (succ zero))
  ≡ @id_func Terminal_cat;

assert ⊢
  @face_realize_func
    (succ zero) (succ zero)
    (@face_identity (succ (succ zero)))
  ≡ @join_map_func
      Terminal_cat Terminal_cat
      Terminal_cat Terminal_cat
      (@id_func Terminal_cat)
      (@id_func Terminal_cat);

assertnot ⊢
  @face_realize_func
    (succ zero) (succ zero)
    (@face_identity (succ (succ zero)))
  ≡ @id_func WalkingArrow_cat;

// A selected branch composition realizes computationally even before whole
// join-map identity is available.
assert ⊢
  @face_realize_func zero (succ zero)
    (@face_comp
      (succ zero)
      (succ (succ zero))
      (succ (succ zero))
      (@face_identity (succ (succ zero)))
      simplex_vertex_zero_code)
  ≡ @comp_cat_fapp0
      Terminal_cat WalkingArrow_cat WalkingArrow_cat
      (@face_realize_func
        (succ zero) (succ zero)
        (@face_identity (succ (succ zero))))
      (@face_realize_func zero (succ zero) simplex_vertex_zero_code);

// The first genuinely new-vertex composite reaches the generic join-map
// composition boundary.
assertnot ⊢
  @face_realize_func (succ zero) (succ (succ (succ zero)))
    (@face_comp
      (succ (succ zero))
      (succ (succ (succ zero)))
      (succ (succ (succ (succ zero))))
      simplex_triangle_zero_one_three_code
      simplex_edge_zero_two_code)
  ≡ @comp_cat_fapp0
      (@DirectedSimplex_cat (succ zero))
      (@DirectedSimplex_cat (succ (succ zero)))
      (@DirectedSimplex_cat (succ (succ (succ zero))))
      (@face_realize_func
        (succ (succ zero)) (succ (succ (succ zero)))
        simplex_triangle_zero_one_three_code)
      (@face_realize_func
        (succ zero) (succ (succ zero))
        simplex_edge_zero_two_code);
