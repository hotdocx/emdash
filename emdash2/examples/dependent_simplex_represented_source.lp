/*
  Reviewer for the constructor-visible represented dependent-simplex source.

  The represented associator of a three-edge Sigma spine supplies the native
  `(kappa,lambda)` tetrahedron input. The existing whole next action preserves
  its base cell, maps its dependent cell through `fdapp1_int_hom_fapp0`, and
  remains iterable at another hom level. No Sigma eta is assumed.
*/

require open emdash.emdash3_2_dependent_simplex_represented_source;

// The two raw bracketings remain distinct runtime terms.
assertnot [K : Cat] (E : τ (Catd K))
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
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23))) ⊢
  @dependent_spine3_left_triangle
    K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23
  ≡ @dependent_spine3_right_triangle
      K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23;

// Mapping the represented tetrahedron preserves its base coherence.
assert [K : Cat] [E D : τ (Catd K)]
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
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23))) ⊢
  sigma_Fst
    (@fapp0
      _ _
      (@dependent_spine3_assoc_map
        K E D FF x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
      (@dependent_spine3_assoc_tetrahedron
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
  ≡ sigma_Fst
      (@dependent_spine3_assoc_cell
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23);

// The dependent component is the next projection of the same internal action.
assert [K : Cat] [E D : τ (Catd K)]
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
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23))) ⊢
  sigma_Snd
    (@fapp0
      _ _
      (@dependent_spine3_assoc_map
        K E D FF x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
      (@dependent_spine3_assoc_tetrahedron
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
  ≡ @fdapp1_int_hom_fapp0
      (Op_cat (Hom_cat K x0 x3))
      (@DependentTriangle_catd K E x0 u0 x3 u3)
      (@DependentTriangleImage_catd K E D FF x0 u0 x3 u3)
      (@fdapp1_int_presheaf_arrow K E D FF x0 u0 x3 u3)
      (sigma_Fst (@dependent_spine3_right_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
      (sigma_Fst (@dependent_spine3_left_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
      (sigma_Fst (@dependent_spine3_assoc_cell
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
      (sigma_Snd (@dependent_spine3_right_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
      (sigma_Snd (@dependent_spine3_left_triangle
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23))
      (sigma_Snd (@dependent_spine3_assoc_cell
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23));

// The specialized map has not capped the recursive tower.
type λ K : Cat, λ E : τ (Catd K), λ D : τ (Catd K),
  λ FF : τ (Functord E D),
  λ x0 : τ (Obj K), λ u0 : τ (Obj (Fibre_cat E x0)),
  λ x1 : τ (Obj K), λ u1 : τ (Obj (Fibre_cat E x1)),
  λ x2 : τ (Obj K), λ u2 : τ (Obj (Fibre_cat E x2)),
  λ x3 : τ (Obj K), λ u3 : τ (Obj (Fibre_cat E x3)),
  λ p01 : τ (Hom K x0 x1),
  λ a01 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x0 u0 x1 u1) p01)),
  λ p12 : τ (Hom K x1 x2),
  λ a12 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x1 u1 x2 u2) p12)),
  λ p23 : τ (Hom K x2 x3),
  λ a23 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x2 u2 x3 u3) p23)),
    @fapp1_func
      _ _
      (@dependent_spine3_assoc_map
        K E D FF x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
      (@dependent_spine3_assoc_tetrahedron
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23)
      (@dependent_spine3_assoc_tetrahedron
        K E x0 x1 x2 x3 u0 u1 u2 u3 p01 a01 p12 a12 p23 a23);
