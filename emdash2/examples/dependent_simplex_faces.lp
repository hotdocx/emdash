/*
  Reviewer for recursive whole nonempty-face action on intrinsic dependent
  simplex codes.

  Dimensions one and two exercise every structural branch: fixed-flag
  constant action, target projection, and outgoing-path map. A selected public
  composite records the honest normalization boundary: target codes and
  constructor-visible observations agree, while opaque whole functors remain
  distinct without an additional uniqueness/extensionality comparison.
*/

require open emdash.emdash3_2_dependent_simplex_faces;

// The two faces of an edge are the fixed source and varying target functors.
assert [C : Cat] (x0 : τ (Obj C)) ⊢
  @dependent_simplex_face_target
    C zero (succ zero)
    (@dependent_simplex_code1 C x0)
    simplex_vertex_zero_code
  ≡ @dependent_simplex_code_zero C;

assert [C : Cat] (x0 : τ (Obj C)) ⊢
  @dependent_simplex_face_func
    C zero (succ zero)
    (@dependent_simplex_code1 C x0)
    simplex_vertex_zero_code
  ≡ @Const_func (@DependentSimplex1_cat C x0) C x0;

assert [C : Cat] (x0 : τ (Obj C)) ⊢
  @dependent_simplex_face_func
    C zero (succ zero)
    (@dependent_simplex_code1 C x0)
    simplex_vertex_one_code
  ≡ @Sigma_proj1_func C (@Rep_catd C x0);

// A constructor-visible triangle exposes all three edge faces.
assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  @fapp0
    (@DependentSimplex2_cat
      C x0 (@dependent_simplex1 C x0 x1 p01))
    (@DependentSimplex1_cat C x0)
    (@dependent_simplex_face_func
      C (succ zero) (succ (succ zero))
      (@dependent_simplex_code2
        C x0 (@dependent_simplex1 C x0 x1 p01))
      simplex_edge_zero_one_code)
    (@dependent_simplex2_visible C x0 x1 x2 p01 p02 p12 alpha012)
  ≡ @dependent_simplex1 C x0 x1 p01;

assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  @fapp0
    (@DependentSimplex2_cat
      C x0 (@dependent_simplex1 C x0 x1 p01))
    (@DependentSimplex1_cat C x0)
    (@dependent_simplex_face_func
      C (succ zero) (succ (succ zero))
      (@dependent_simplex_code2
        C x0 (@dependent_simplex1 C x0 x1 p01))
      simplex_edge_zero_two_code)
    (@dependent_simplex2_visible C x0 x1 x2 p01 p02 p12 alpha012)
  ≡ @dependent_simplex1 C x0 x2 p02;

assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  @fapp0
    (@DependentSimplex2_cat
      C x0 (@dependent_simplex1 C x0 x1 p01))
    (@DependentSimplex1_cat C x1)
    (@dependent_simplex_face_func
      C (succ zero) (succ (succ zero))
      (@dependent_simplex_code2
        C x0 (@dependent_simplex1 C x0 x1 p01))
      simplex_edge_one_two_code)
    (@dependent_simplex2_visible C x0 x1 x2 p01 p02 p12 alpha012)
  ≡ @dependent_simplex1 C x1 x2 p12;

// Every selected face remains a whole functor at the next hom level.
type λ C : Cat,
  λ x0 : τ (Obj C),
  λ e01 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ t0 : τ (Obj (@DependentSimplex2_cat C x0 e01)),
  λ t1 : τ (Obj (@DependentSimplex2_cat C x0 e01)),
    @fapp1_func
      (@DependentSimplex2_cat C x0 e01)
      _
      (@dependent_simplex_face_func
        C (succ zero) (succ (succ zero))
        (@dependent_simplex_code2 C x0 e01)
        simplex_edge_zero_two_code)
      t0 t1;

// Public FaceCode composition owns the selected vertex-of-edge composite.
assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0))) ⊢
  @dependent_simplex_face_target
    C zero (succ (succ zero))
    (@dependent_simplex_code2 C x0 e01)
    (@face_comp
      (succ zero)
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_zero_two_code
      simplex_vertex_one_code)
  ≡ @dependent_simplex_face_target
      C zero (succ zero)
      (@dependent_simplex_face_target
        C (succ zero) (succ (succ zero))
        (@dependent_simplex_code2 C x0 e01)
        simplex_edge_zero_two_code)
      simplex_vertex_one_code;

// The direct and sequential opaque whole functors deliberately do not become
// judgmentally equal merely because their FaceCode indices compose.
assertnot [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0))) ⊢
  @dependent_simplex_face_func
    C zero (succ (succ zero))
    (@dependent_simplex_code2 C x0 e01)
    (@face_comp
      (succ zero)
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_zero_two_code
      simplex_vertex_one_code)
  ≡ @comp_cat_fapp0
      (@DependentSimplex2_cat C x0 e01)
      (@dependent_simplex_code_decode_cat
        C (succ zero)
        (@dependent_simplex_face_target
          C (succ zero) (succ (succ zero))
          (@dependent_simplex_code2 C x0 e01)
          simplex_edge_zero_two_code))
      C
      (@dependent_simplex_face_func
        C zero (succ zero)
        (@dependent_simplex_face_target
          C (succ zero) (succ (succ zero))
          (@dependent_simplex_code2 C x0 e01)
          simplex_edge_zero_two_code)
        simplex_vertex_one_code)
      (@dependent_simplex_face_func
        C (succ zero) (succ (succ zero))
        (@dependent_simplex_code2 C x0 e01)
        simplex_edge_zero_two_code);

// Both routes nevertheless compute to the same final vertex on a visible
// triangle, without adding a functor-composition rewrite.
assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  @fapp0
    (@DependentSimplex2_cat
      C x0 (@dependent_simplex1 C x0 x1 p01))
    C
    (@dependent_simplex_face_func
      C zero (succ (succ zero))
      (@dependent_simplex_code2
        C x0 (@dependent_simplex1 C x0 x1 p01))
      (@face_comp
        (succ zero)
        (succ (succ zero))
        (succ (succ (succ zero)))
        simplex_edge_zero_two_code
        simplex_vertex_one_code))
    (@dependent_simplex2_visible C x0 x1 x2 p01 p02 p12 alpha012)
  ≡ x2;

assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  @fapp0
    (@DependentSimplex2_cat
      C x0 (@dependent_simplex1 C x0 x1 p01))
    C
    (@comp_cat_fapp0
      (@DependentSimplex2_cat
        C x0 (@dependent_simplex1 C x0 x1 p01))
      (@DependentSimplex1_cat C x0)
      C
      (@dependent_simplex_face_func
        C zero (succ zero)
        (@dependent_simplex_code1 C x0)
        simplex_vertex_one_code)
      (@dependent_simplex_face_func
        C (succ zero) (succ (succ zero))
        (@dependent_simplex_code2
          C x0 (@dependent_simplex1 C x0 x1 p01))
        simplex_edge_zero_two_code))
    (@dependent_simplex2_visible C x0 x1 x2 p01 p02 p12 alpha012)
  ≡ x2;
