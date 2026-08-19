/*
  Constructor-visible represented source for the recursive dependent simplex.

  A three-edge spine in a Sigma total has two bracketed composite arrows. The
  generic represented associator supplies a directed cell between them. When
  the vertices and edges remain at their native `Struct_sigma`/
  `dependent_triangle` constructors, the active Hom(Sigma) computation exposes
  that cell as the dependent pair `(kappa,lambda)` required by
  `dependent_tetrahedron`.

  The whole `dependent_spine3_assoc_map` is only a specialization of the
  existing next internal action. Its visible object action preserves `kappa`
  and maps `lambda` through `fdapp1_int_hom_fapp0`; its next hom action remains
  available through the generic `fapp1_func` owner. No Sigma eta, coherence
  record, runtime rule, or unifier is added.
*/

require open emdash.emdash3_2_dependent_simplex_path_associator;
require open emdash.emdash3_2_dependent_simplex_bridge;

// Left bracketing of three constructor-visible arrows in the Sigma total.
symbol dependent_spine3_left_triangle
  [K : Cat]
  (E : τ (Catd K))
  [x0 x1 x2 x3 : τ (Obj K)]
  [u0 : τ (Obj (Fibre_cat E x0))]
  [u1 : τ (Obj (Fibre_cat E x1))]
  [u2 : τ (Obj (Fibre_cat E x2))]
  [u3 : τ (Obj (Fibre_cat E x3))]
  (p01 : τ (Hom K x0 x1))
  (a01 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x0 u0 x1 u1) p01)))
  (p12 : τ (Hom K x1 x2))
  (a12 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x1 u1 x2 u2) p12)))
  (p23 : τ (Hom K x2 x3))
  (a23 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23)))
  : τ (Obj (@DependentTriangle_cat K E x0 u0 x3 u3))
≔ @comp_fapp0
    (@Sigma_cat K E)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x0 u0)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x1 u1)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x3 u3)
    (@comp_fapp0
      (@Sigma_cat K E)
      (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x1 u1)
      (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x2 u2)
      (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x3 u3)
      (@dependent_triangle K E x2 u2 x3 u3 p23 a23)
      (@dependent_triangle K E x1 u1 x2 u2 p12 a12))
    (@dependent_triangle K E x0 u0 x1 u1 p01 a01);

// Right bracketing of the same three constructor-visible arrows.
symbol dependent_spine3_right_triangle
  [K : Cat]
  (E : τ (Catd K))
  [x0 x1 x2 x3 : τ (Obj K)]
  [u0 : τ (Obj (Fibre_cat E x0))]
  [u1 : τ (Obj (Fibre_cat E x1))]
  [u2 : τ (Obj (Fibre_cat E x2))]
  [u3 : τ (Obj (Fibre_cat E x3))]
  (p01 : τ (Hom K x0 x1))
  (a01 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x0 u0 x1 u1) p01)))
  (p12 : τ (Hom K x1 x2))
  (a12 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x1 u1 x2 u2) p12)))
  (p23 : τ (Hom K x2 x3))
  (a23 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23)))
  : τ (Obj (@DependentTriangle_cat K E x0 u0 x3 u3))
≔ @comp_fapp0
    (@Sigma_cat K E)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x0 u0)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x2 u2)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x3 u3)
    (@dependent_triangle K E x2 u2 x3 u3 p23 a23)
    (@comp_fapp0
      (@Sigma_cat K E)
      (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x0 u0)
      (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x1 u1)
      (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x2 u2)
      (@dependent_triangle K E x1 u1 x2 u2 p12 a12)
      (@dependent_triangle K E x0 u0 x1 u1 p01 a01));

// Generic represented associator at those two native dependent endpoints.
symbol dependent_spine3_assoc_cell
  [K : Cat]
  (E : τ (Catd K))
  [x0 x1 x2 x3 : τ (Obj K)]
  [u0 : τ (Obj (Fibre_cat E x0))]
  [u1 : τ (Obj (Fibre_cat E x1))]
  [u2 : τ (Obj (Fibre_cat E x2))]
  [u3 : τ (Obj (Fibre_cat E x3))]
  (p01 : τ (Hom K x0 x1))
  (a01 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x0 u0 x1 u1) p01)))
  (p12 : τ (Hom K x1 x2))
  (a12 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x1 u1 x2 u2) p12)))
  (p23 : τ (Hom K x2 x3))
  (a23 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23)))
  : τ (Obj (@Hom_cat
      (@DependentTriangle_cat K E x0 u0 x3 u3)
      (@dependent_spine3_left_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
      (@dependent_spine3_right_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)))
≔ @represented_assoc_readable_cell
    (@Sigma_cat K E)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x0 u0)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x1 u1)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x2 u2)
    (@Struct_sigma (Obj K) (λ x : τ (Obj K), Obj (Fibre_cat E x)) x3 u3)
    (@dependent_triangle K E x0 u0 x1 u1 p01 a01)
    (@dependent_triangle K E x1 u1 x2 u2 p12 a12)
    (@dependent_triangle K E x2 u2 x3 u3 p23 a23);

// Constructor view of the same cell as the native `(kappa,lambda)` source.
symbol dependent_spine3_assoc_tetrahedron
  [K : Cat]
  (E : τ (Catd K))
  [x0 x1 x2 x3 : τ (Obj K)]
  [u0 : τ (Obj (Fibre_cat E x0))]
  [u1 : τ (Obj (Fibre_cat E x1))]
  [u2 : τ (Obj (Fibre_cat E x2))]
  [u3 : τ (Obj (Fibre_cat E x3))]
  (p01 : τ (Hom K x0 x1))
  (a01 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x0 u0 x1 u1) p01)))
  (p12 : τ (Hom K x1 x2))
  (a12 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x1 u1 x2 u2) p12)))
  (p23 : τ (Hom K x2 x3))
  (a23 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23)))
  : τ (Obj (@Hom_cat
      (@DependentTriangle_cat K E x0 u0 x3 u3)
      (@dependent_spine3_left_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
      (@dependent_spine3_right_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)))
≔ @dependent_tetrahedron
    K E x0 u0 x3 u3
    (sigma_Fst (@dependent_spine3_left_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Fst (@dependent_spine3_right_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Snd (@dependent_spine3_left_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Snd (@dependent_spine3_right_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Fst (@dependent_spine3_assoc_cell
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Snd (@dependent_spine3_assoc_cell
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23));

// Whole next action specialized to the constructor-visible source endpoints.
symbol dependent_spine3_assoc_map
  [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  [x0 x1 x2 x3 : τ (Obj K)]
  [u0 : τ (Obj (Fibre_cat E x0))]
  [u1 : τ (Obj (Fibre_cat E x1))]
  [u2 : τ (Obj (Fibre_cat E x2))]
  [u3 : τ (Obj (Fibre_cat E x3))]
  (p01 : τ (Hom K x0 x1))
  (a01 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x0 u0 x1 u1) p01)))
  (p12 : τ (Hom K x1 x2))
  (a12 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x1 u1 x2 u2) p12)))
  (p23 : τ (Hom K x2 x3))
  (a23 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23)))
  : τ (Functor
      (@Hom_cat
        (@DependentTriangle_cat K E x0 u0 x3 u3)
        (@dependent_spine3_left_triangle
          K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
        (@dependent_spine3_right_triangle
          K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
      (@Hom_cat
        (@DependentTriangleImage_cat K E D FF x0 u0 x3 u3)
        (@fapp0
          (@DependentTriangle_cat K E x0 u0 x3 u3)
          (@DependentTriangleImage_cat K E D FF x0 u0 x3 u3)
          (@dependent_triangle_map K E D FF x0 u0 x3 u3)
          (@dependent_spine3_left_triangle
            K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
        (@fapp0
          (@DependentTriangle_cat K E x0 u0 x3 u3)
          (@DependentTriangleImage_cat K E D FF x0 u0 x3 u3)
          (@dependent_triangle_map K E D FF x0 u0 x3 u3)
          (@dependent_spine3_right_triangle
            K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))))
≔ @dependent_tetrahedron_map
    K E D FF x0 u0 x3 u3
    (sigma_Fst (@dependent_spine3_left_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Fst (@dependent_spine3_right_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Snd (@dependent_spine3_left_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
    (sigma_Snd (@dependent_spine3_right_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23));
