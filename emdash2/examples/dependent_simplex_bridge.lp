/*
  Reviewer for the recursive dependent-simplex bridge.

  The first layer is exactly Hom(Sigma(E)); its map is the first hom action of
  Sigma(FF). The next action maps a visible tetrahedron (kappa,lambda) to the
  same base cell together with fdapp1_int_hom_fapp0(...,lambda), and retains a
  further hom action. Two transparent face functors project a volume to its
  base surface and target-fibre endpoint surface. The ordinary specialization
  recovers the active functor compositor without a second coherence record.
*/

require open emdash.emdash3_2_dependent_simplex_bridge;

// The triangle classifier is the active Hom(Sigma) presentation.
assert (K : Cat) (E : τ (Catd K))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y))) ⊢
  @Hom_cat
    (@Sigma_cat K E)
    (@Struct_sigma (Obj K)
      (λ k : τ (Obj K), Obj (Fibre_cat E k)) x u)
    (@Struct_sigma (Obj K)
      (λ k : τ (Obj K), Obj (Fibre_cat E k)) y v)
  ≡ @DependentTriangle_cat K E x u y v;

// The two whole projections expose the base line and the target-fibre
// endpoint while retaining functor action on volumes.
assert (K : Cat) (E : τ (Catd K))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p))) ⊢
  @fapp0
    (@DependentTriangle_cat K E x u y v)
    (Hom_cat K x y)
    (@dependent_triangle_base_face_func K E x u y v)
    (@dependent_triangle K E x u y v p alpha)
  ≡ p;

assert (K : Cat) (E : τ (Catd K))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p))) ⊢
  @fapp0
    (@DependentTriangle_cat K E x u y v)
    (Fibre_cat E y)
    (@dependent_triangle_endpoint_face_func K E x u y v)
    (@dependent_triangle K E x u y v p alpha)
  ≡ @fapp0
      (Hom_cat K x y)
      (Fibre_cat E y)
      (@fib_cov_tapp0_func K E x y u)
      p;

// The two projections are one packaged whole boundary functor.
assert (K : Cat) (E : τ (Catd K))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y)))
  (p : τ (Hom K x y))
  (alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p))) ⊢
  @fapp0
    (@DependentTriangle_cat K E x u y v)
    (Product_cat (Hom_cat K x y) (Fibre_cat E y))
    (@dependent_triangle_boundary_face_func K E x u y v)
    (@dependent_triangle K E x u y v p alpha)
  ≡ @Struct_sigma
      (Obj (Hom_cat K x y))
      (λ _ : τ (Obj (Hom_cat K x y)), Obj (Fibre_cat E y))
      p
      (@fapp0
        (Hom_cat K x y)
        (Fibre_cat E y)
        (@fib_cov_tapp0_func K E x y u)
        p);

// Both projection functors retain another hom action on a volume.
type λ K : Cat, λ E : τ (Catd K),
  λ x : τ (Obj K), λ u : τ (Obj (Fibre_cat E x)),
  λ y : τ (Obj K), λ v : τ (Obj (Fibre_cat E y)),
  λ p : τ (Hom K x y), λ q : τ (Hom K x y),
  λ alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p)),
  λ beta : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) q)),
    @fapp1_func
      (@DependentTriangle_cat K E x u y v)
      (Hom_cat K x y)
      (@dependent_triangle_base_face_func K E x u y v)
      (@dependent_triangle K E x u y v p alpha)
      (@dependent_triangle K E x u y v q beta);

type λ K : Cat, λ E : τ (Catd K),
  λ x : τ (Obj K), λ u : τ (Obj (Fibre_cat E x)),
  λ y : τ (Obj K), λ v : τ (Obj (Fibre_cat E y)),
  λ p : τ (Hom K x y), λ q : τ (Hom K x y),
  λ alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p)),
  λ beta : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) q)),
    @fapp1_func
      (@DependentTriangle_cat K E x u y v)
      (Fibre_cat E y)
      (@dependent_triangle_endpoint_face_func K E x u y v)
      (@dependent_triangle K E x u y v p alpha)
      (@dependent_triangle K E x u y v q beta);

// Its whole map is exactly the existing first hom action of Sigma(FF).
assert (K : Cat) (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y))) ⊢
  @dependent_triangle_map K E D FF x u y v
  ≡ @fapp1_func
      (@Sigma_cat K E)
      (@Sigma_cat K D)
      (@sigma_map_func K E D FF)
      (@Struct_sigma (Obj K)
        (λ k : τ (Obj K), Obj (Fibre_cat E k)) x u)
      (@Struct_sigma (Obj K)
        (λ k : τ (Obj K), Obj (Fibre_cat E k)) y v);

// On a visible higher constructor, the second action preserves kappa.
assert (K : Cat) (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y)))
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
    kappa))) ⊢
  sigma_Fst
    (@dependent_tetrahedron_image
      K E D FF x u y v p0 p1 alpha0 alpha1
      (@dependent_tetrahedron
        K E x u y v p0 p1 alpha0 alpha1 kappa lambda))
  ≡ kappa;

// Its dependent component is the next projection of the same internal action.
assert (K : Cat) (E D : τ (Catd K)) (FF : τ (Functord E D))
  (x : τ (Obj K)) (u : τ (Obj (Fibre_cat E x)))
  (y : τ (Obj K)) (v : τ (Obj (Fibre_cat E y)))
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
    kappa))) ⊢
  sigma_Snd
    (@dependent_tetrahedron_image
      K E D FF x u y v p0 p1 alpha0 alpha1
      (@dependent_tetrahedron
        K E x u y v p0 p1 alpha0 alpha1 kappa lambda))
  ≡ @fdapp1_int_hom_fapp0
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v)
      (@DependentTriangleImage_catd K E D FF x u y v)
      (@fdapp1_int_presheaf_arrow K E D FF x u y v)
      p1 p0 kappa alpha1 alpha0 lambda;

// A further hom action remains available; the bridge has not capped the
// recursive tower at the tetrahedron.
type λ K : Cat, λ E : τ (Catd K), λ D : τ (Catd K),
  λ FF : τ (Functord E D),
  λ x : τ (Obj K), λ u : τ (Obj (Fibre_cat E x)),
  λ y : τ (Obj K), λ v : τ (Obj (Fibre_cat E y)),
  λ p0 : τ (Hom K x y), λ p1 : τ (Hom K x y),
  λ alpha0 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p0)),
  λ alpha1 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p1)),
  λ theta0 : τ (Obj (@Hom_cat
    (@DependentTriangle_cat K E x u y v)
    (@dependent_triangle K E x u y v p0 alpha0)
    (@dependent_triangle K E x u y v p1 alpha1))),
  λ theta1 : τ (Obj (@Hom_cat
    (@DependentTriangle_cat K E x u y v)
    (@dependent_triangle K E x u y v p0 alpha0)
    (@dependent_triangle K E x u y v p1 alpha1))),
    @fapp1_func
      (@Hom_cat
        (@DependentTriangle_cat K E x u y v)
        (@dependent_triangle K E x u y v p0 alpha0)
        (@dependent_triangle K E x u y v p1 alpha1))
      _
      (@dependent_tetrahedron_map
        K E D FF x u y v p0 p1 alpha0 alpha1)
      theta0 theta1;

// Ordinary functor specialization.
symbol ordinary_compositor_source_catd
  [A : Cat]
  (X0 : τ (Obj A))
  : τ (Catd A)
≔ @hom_ A A (@id_func A) X0;

symbol ordinary_compositor_target_catd
  [A B : Cat]
  (F : τ (Functor A B))
  (X0 : τ (Obj A))
  : τ (Catd A)
≔ @hom_ B A F (@fapp0 A B F X0);

symbol ordinary_compositor_gf
  [A : Cat]
  [X0 X1 X2 : τ (Obj A)]
  (g : τ (Hom A X1 X2))
  (f : τ (Hom A X0 X1))
  : τ (Obj (Fibre_cat (@ordinary_compositor_source_catd A X0) X2))
≔ @fapp0
    (Fibre_cat (@ordinary_compositor_source_catd A X0) X1)
    (Fibre_cat (@ordinary_compositor_source_catd A X0) X2)
    (@catd_transport_func
      A (@ordinary_compositor_source_catd A X0) X1 X2 g)
    f;

symbol ordinary_compositor_source_triangle
  [A : Cat]
  [X0 X1 X2 : τ (Obj A)]
  (g : τ (Hom A X1 X2))
  (f : τ (Hom A X0 X1))
  : τ (Obj
      (@DependentTriangle_cat
        A (@ordinary_compositor_source_catd A X0)
        X1 f X2 (@ordinary_compositor_gf A X0 X1 X2 g f)))
≔ @dependent_triangle
    A (@ordinary_compositor_source_catd A X0)
    X1 f X2 (@ordinary_compositor_gf A X0 X1 X2 g f)
    g
    (@id
      (Fibre_cat (@ordinary_compositor_source_catd A X0) X2)
      (@ordinary_compositor_gf A X0 X1 X2 g f));

// The image component is the direct internal-action projection.
assert (A B : Cat) (F : τ (Functor A B))
  (X0 X1 X2 : τ (Obj A))
  (f : τ (Hom A X0 X1))
  (g : τ (Hom A X1 X2)) ⊢
  sigma_Snd
    (@fapp0
      (@DependentTriangle_cat
        A (@ordinary_compositor_source_catd A X0)
        X1 f X2 (@ordinary_compositor_gf A X0 X1 X2 g f))
      (@DependentTriangleImage_cat
        A
        (@ordinary_compositor_source_catd A X0)
        (@ordinary_compositor_target_catd A B F X0)
        (@fapp1_at_transf A B F X0)
        X1 f X2 (@ordinary_compositor_gf A X0 X1 X2 g f))
      (@dependent_triangle_map
        A
        (@ordinary_compositor_source_catd A X0)
        (@ordinary_compositor_target_catd A B F X0)
        (@fapp1_at_transf A B F X0)
        X1 f X2 (@ordinary_compositor_gf A X0 X1 X2 g f))
      (@ordinary_compositor_source_triangle A X0 X1 X2 g f))
  ≡ @fapp0
      _ _
      (@fdapp1_int_hom_func
        A
        (@ordinary_compositor_source_catd A X0)
        (@ordinary_compositor_target_catd A B F X0)
        (@fapp1_at_transf A B F X0)
        X1 X2 g f (@ordinary_compositor_gf A X0 X1 X2 g f))
      (@id
        (Fibre_cat (@ordinary_compositor_source_catd A X0) X2)
        (@ordinary_compositor_gf A X0 X1 X2 g f));

// The dimension-two cell is exactly the active functor compositor.
assert (A B : Cat) (F : τ (Functor A B))
  (X0 X1 X2 : τ (Obj A))
  (f : τ (Hom A X0 X1))
  (g : τ (Hom A X1 X2)) ⊢
  @fapp1_compositor A B F X0 X1 X2 g f
  ≡ @fdapp1_int_cell
      A
      (@ordinary_compositor_source_catd A X0)
      (@ordinary_compositor_target_catd A B F X0)
      (@fapp1_at_transf A B F X0)
      X1 X2 g f;
