/*
  Focused reviewer for augmented semi-simplex face-map codes.

  Raw skip/keep syntax owns structural recursion.  The public FaceCode is its
  classified set truncation, whose constructors and composition still
  compute through the active restricted recursor.  These checks deliberately
  stop before constructing the internal semi-simplex category.
*/

require open emdash.emdash3_2_semisimplicial_face_codes;

// Every public hom-code carrier is intrinsically a set.
assert (p n : τ Nat_grpd) ⊢
  @face_code_is_set p n
  : τ (IsSetGrpd (@FaceCode p n));

// Public constructors retain the raw point computation of trunc_map.
assert ⊢
  @face_skip zero zero face_nil
  ≡ @trunc_intro
      trunc_zero
      (@RawFaceCode zero (succ zero))
      (@raw_face_skip zero zero raw_face_nil);

assert ⊢
  @face_keep zero zero face_nil
  ≡ @trunc_intro
      trunc_zero
      (@RawFaceCode (succ zero) (succ zero))
      (@raw_face_keep zero zero raw_face_nil);

// Identity is the all-keep word.
assert ⊢
  @face_identity zero
  ≡ face_nil;

assert ⊢
  @face_identity (succ zero)
  ≡ @face_keep zero zero face_nil;

// The two vertices of the directed one-simplex.
symbol face_vertex_zero
  : τ (@FaceCode (succ zero) (succ (succ zero)))
≔ @face_skip
    (succ zero) (succ zero)
    (@face_keep zero zero face_nil);

symbol face_vertex_one
  : τ (@FaceCode (succ zero) (succ (succ zero)))
≔ @face_keep
    zero (succ zero)
    (@face_skip zero zero face_nil);

// The first edge of the directed two-simplex omits its last vertex.
symbol face_edge_zero_one
  : τ (@FaceCode
      (succ (succ zero))
      (succ (succ (succ zero))))
≔ @face_skip
    (succ (succ zero))
    (succ (succ zero))
    (@face_identity (succ (succ zero)));

// Right and left identity compute on visible codes.
assert ⊢
  @face_comp
    (succ zero) (succ zero) (succ (succ zero))
    face_vertex_zero
    (@face_identity (succ zero))
  ≡ face_vertex_zero;

assert ⊢
  @face_comp
    (succ zero) (succ (succ zero)) (succ (succ zero))
    (@face_identity (succ (succ zero)))
    face_vertex_one
  ≡ face_vertex_one;

/*
  A keep in the outer code composed with a skip in the inner code takes the
  mixed structural branch and yields the unique empty face of a two-vertex
  ordinal.
*/
assert ⊢
  @face_comp
    zero (succ zero) (succ (succ zero))
    face_vertex_one
    (@face_skip zero zero face_nil)
  ≡ @face_skip zero (succ zero)
      (@face_skip zero zero face_nil);

// A closed three-map chain validates both structural association orders.
assert ⊢
  @face_comp
    zero
    (succ (succ zero))
    (succ (succ (succ zero)))
    face_edge_zero_one
    (@face_comp
      zero
      (succ zero)
      (succ (succ zero))
      face_vertex_one
      (@face_skip zero zero face_nil))
  ≡ @face_comp
      zero
      (succ zero)
      (succ (succ (succ zero)))
      (@face_comp
        (succ zero)
        (succ (succ zero))
        (succ (succ (succ zero)))
        face_edge_zero_one
        face_vertex_one)
      (@face_skip zero zero face_nil);

// Indices are retained: a vertex code is not an edge code.
assertnot ⊢
  face_vertex_zero
  : τ (@FaceCode (succ (succ zero)) (succ (succ zero)));
