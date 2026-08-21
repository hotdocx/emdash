/*
  Recursive dependent-simplex presentation of the internal hom action.

  For fixed total endpoints (x,u) and (y,v), a dependent triangle is the
  Sigma-of-homd presentation already emitted by Hom(Sigma(E)):

    (p,alpha),  p : x -> y,
                alpha : E[p](u) -> v.

  A displayed functor FF maps that whole triangle classifier through the
  existing fdapp1_int_presheaf_arrow. The resulting whole functor is exactly
  the first hom action of Sigma(FF). Its next hom action is therefore the
  tetrahedron map; on a visible higher constructor (kappa,lambda), the base
  cell is retained and the dependent component computes through the existing
  fdapp1_int_hom_fapp0 owner.

  Before applying FF, the triangle classifier retains its two lower face
  projections as whole functors.  One exposes the Sigma/base line; the other
  evaluates that line at the fixed source endpoint in the target fibre.  On a
  volume their hom actions are the base and fourth surfaces, respectively.

  This is a transparent recursive bridge, not a standalone tetrahedron or an
  external coherence record. It adds no rule or unifier and does not claim a
  whole comparison with Functor_cat(DirectedSimplex_cat(n),C), which remains
  gated by join uniqueness and whole face functoriality.
*/

require open emdash.emdash3_2_face_realization;

// First dependent-hom simplex family for fixed total endpoints.
symbol DependentTriangle_catd
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Catd (Op_cat (Hom_cat K x y)))
≔ @homd_ K E E (@id_funcd K E) x u y v;

// Total triangle classifier, in the orientation selected by Hom(Sigma(E)).
symbol DependentTriangle_cat
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : Cat
≔ @Op_cat
    (@Sigma_cat
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v));

/*
  The dependent-triangle classifier is doubly fibred over lower-dimensional
  data.  The first whole face functor remembers the base arrow.  The second
  keeps the fixed source endpoint and evaluates that base arrow in the target
  fibre.  Consequently, on an arrow between dependent triangles, their hom
  actions expose respectively the base surface and the fourth endpoint-action
  surface of the recursive tetrahedron.

  These are transparent projections of the existing homd_/Sigma owner.  They
  add no face equation, rule, unifier, or capped component normal form.
*/

// Base-line projection: (p,alpha) |-> p.
symbol dependent_triangle_base_face_func
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor
      (@DependentTriangle_cat K E x u y v)
      (Hom_cat K x y))
≔ @Op_func
    (@Sigma_cat
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v))
    (Op_cat (Hom_cat K x y))
    (@Sigma_proj1_func
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v));

// Target-fibre endpoint projection: (p,alpha) |-> E[p](u).
symbol dependent_triangle_endpoint_face_func
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor
      (@DependentTriangle_cat K E x u y v)
      (Fibre_cat E y))
≔ @comp_cat_fapp0
    (@DependentTriangle_cat K E x u y v)
    (Hom_cat K x y)
    (Fibre_cat E y)
    (@fib_cov_tapp0_func K E x y u)
    (@dependent_triangle_base_face_func K E x u y v);

// Whole paired boundary projection. Product projections recover the base-line
// and target-fibre endpoint functors above; its hom action sends a volume to
// the pair (base surface, fourth surface).
symbol dependent_triangle_boundary_face_func
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor
      (@DependentTriangle_cat K E x u y v)
      (Product_cat (Hom_cat K x y) (Fibre_cat E y)))
≔ @Struct_sigma
    (Obj (Functor_cat
      (@DependentTriangle_cat K E x u y v)
      (Hom_cat K x y)))
    (λ _ : τ (Obj (Functor_cat
        (@DependentTriangle_cat K E x u y v)
        (Hom_cat K x y))),
      Obj (Functor_cat
        (@DependentTriangle_cat K E x u y v)
        (Fibre_cat E y)))
    (@dependent_triangle_base_face_func K E x u y v)
    (@dependent_triangle_endpoint_face_func K E x u y v);

// A triangle is one base arrow paired with its dependent fibre arrow.
symbol dependent_triangle
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p)))
  : τ (Obj (@DependentTriangle_cat K E x u y v))
≔ @Struct_sigma
    (Obj (Op_cat (Hom_cat K x y)))
    (λ r : τ (Obj (Op_cat (Hom_cat K x y))),
      Obj (Fibre_cat (@DependentTriangle_catd K E x u y v) r))
    p alpha;

// Target dependent-hom family after applying FF at the source endpoint.
symbol DependentTriangleImage_catd
  [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Catd (Op_cat (Hom_cat K x y)))
≔ @homd_
    K E D FF
    x
    (@fapp0
      (Fibre_cat E x)
      (Fibre_cat D x)
      (@Fibre_func K E D FF x) u)
    y v;

symbol DependentTriangleImage_cat
  [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : Cat
≔ @Op_cat
    (@Sigma_cat
      (Op_cat (Hom_cat K x y))
      (@DependentTriangleImage_catd K E D FF x u y v));

// Whole first action. The displayed map is the active internal-action
// projection, not a separately postulated transformation.
symbol dependent_triangle_map
  [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  : τ (Functor
      (@DependentTriangle_cat K E x u y v)
      (@DependentTriangleImage_cat K E D FF x u y v))
≔ @Op_func
    (@Sigma_cat
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v))
    (@Sigma_cat
      (Op_cat (Hom_cat K x y))
      (@DependentTriangleImage_catd K E D FF x u y v))
    (@sigma_map_func
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v)
      (@DependentTriangleImage_catd K E D FF x u y v)
      (@fdapp1_int_presheaf_arrow K E D FF x u y v));

// Next action between two source triangles. This is the generic tetrahedron
// map and remains iterable at another hom level.
symbol dependent_tetrahedron_map
  [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  (p0 p1 : τ (Hom K x y))
  (alpha0 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p0)))
  (alpha1 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p1)))
  : τ (Functor
      (@Hom_cat
        (@DependentTriangle_cat K E x u y v)
        (@dependent_triangle K E x u y v p0 alpha0)
        (@dependent_triangle K E x u y v p1 alpha1))
      (@Hom_cat
        (@DependentTriangleImage_cat K E D FF x u y v)
        (@fapp0
          (@DependentTriangle_cat K E x u y v)
          (@DependentTriangleImage_cat K E D FF x u y v)
          (@dependent_triangle_map K E D FF x u y v)
          (@dependent_triangle K E x u y v p0 alpha0))
        (@fapp0
          (@DependentTriangle_cat K E x u y v)
          (@DependentTriangleImage_cat K E D FF x u y v)
          (@dependent_triangle_map K E D FF x u y v)
          (@dependent_triangle K E x u y v p1 alpha1))))
≔ @fapp1_func
    (@DependentTriangle_cat K E x u y v)
    (@DependentTriangleImage_cat K E D FF x u y v)
    (@dependent_triangle_map K E D FF x u y v)
    (@dependent_triangle K E x u y v p0 alpha0)
    (@dependent_triangle K E x u y v p1 alpha1);

// Constructor view of a higher cell between two dependent triangles.
symbol dependent_tetrahedron
  [K : Cat]
  (E : τ (Catd K))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  (p0 p1 : τ (Hom K x y))
  (alpha0 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p0)))
  (alpha1 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p1)))
  (kappa : τ (Hom (Op_cat (Hom_cat K x y)) p1 p0))
  (lambda : τ (Obj (Fibre_cat
    (@homd_
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v)
      (@DependentTriangle_catd K E x u y v)
      (@id_funcd
        (Op_cat (Hom_cat K x y))
        (@DependentTriangle_catd K E x u y v))
      p1 alpha1 p0 alpha0)
    kappa)))
  : τ (Obj
      (@Hom_cat
        (@DependentTriangle_cat K E x u y v)
        (@dependent_triangle K E x u y v p0 alpha0)
        (@dependent_triangle K E x u y v p1 alpha1)))
≔ @Struct_sigma
    (Obj (Op_cat
      (Hom_cat (Op_cat (Hom_cat K x y)) p1 p0)))
    (λ r : τ (Obj (Op_cat
        (Hom_cat (Op_cat (Hom_cat K x y)) p1 p0))),
      Obj (Fibre_cat
        (@homd_
          (Op_cat (Hom_cat K x y))
          (@DependentTriangle_catd K E x u y v)
          (@DependentTriangle_catd K E x u y v)
          (@id_funcd
            (Op_cat (Hom_cat K x y))
            (@DependentTriangle_catd K E x u y v))
          p1 alpha1 p0 alpha0)
        r))
    kappa lambda;

// Apply the generic next action to one higher dependent cell.
symbol dependent_tetrahedron_image
  [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (x : τ (Obj K))
  (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K))
  (v : τ (Obj (Fibre_cat E y)))
  (p0 p1 : τ (Hom K x y))
  (alpha0 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p0)))
  (alpha1 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p1)))
  (theta : τ (Obj
    (@Hom_cat
      (@DependentTriangle_cat K E x u y v)
      (@dependent_triangle K E x u y v p0 alpha0)
      (@dependent_triangle K E x u y v p1 alpha1))))
  : τ (Obj
      (@Hom_cat
        (@DependentTriangleImage_cat K E D FF x u y v)
        (@fapp0
          (@DependentTriangle_cat K E x u y v)
          (@DependentTriangleImage_cat K E D FF x u y v)
          (@dependent_triangle_map K E D FF x u y v)
          (@dependent_triangle K E x u y v p0 alpha0))
        (@fapp0
          (@DependentTriangle_cat K E x u y v)
          (@DependentTriangleImage_cat K E D FF x u y v)
          (@dependent_triangle_map K E D FF x u y v)
          (@dependent_triangle K E x u y v p1 alpha1))))
≔ @fapp0
    (@Hom_cat
      (@DependentTriangle_cat K E x u y v)
      (@dependent_triangle K E x u y v p0 alpha0)
      (@dependent_triangle K E x u y v p1 alpha1))
    (@Hom_cat
      (@DependentTriangleImage_cat K E D FF x u y v)
      (@fapp0
        (@DependentTriangle_cat K E x u y v)
        (@DependentTriangleImage_cat K E D FF x u y v)
        (@dependent_triangle_map K E D FF x u y v)
        (@dependent_triangle K E x u y v p0 alpha0))
      (@fapp0
        (@DependentTriangle_cat K E x u y v)
        (@DependentTriangleImage_cat K E D FF x u y v)
        (@dependent_triangle_map K E D FF x u y v)
        (@dependent_triangle K E x u y v p1 alpha1)))
    (@dependent_tetrahedron_map K E D FF x u y v p0 p1 alpha0 alpha1)
    theta;
