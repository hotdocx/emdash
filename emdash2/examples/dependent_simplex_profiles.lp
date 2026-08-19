/*
  General lax, selected strict, and Path readings of the recursive dependent
  simplex bridge. No profile-specific simplex classifier is introduced.
*/

require open emdash.emdash3_2_dependent_simplex_bridge;
require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_path_pseudo_laxity;

injective symbol dependent_simplex_unprofiled_functor
  (A B : Cat)
  : τ (Functor A B);

// General ambient functors retain a noncollapsed compositor.
assertnot [A B : Cat]
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor
    A B (@dependent_simplex_unprofiled_functor A B) X Y Z g f
  ≡ @id
      (Hom_cat B
        (@fapp0 A B (@dependent_simplex_unprofiled_functor A B) X)
        (@fapp0 A B (@dependent_simplex_unprofiled_functor A B) Z))
      (@strict_functor_compositor_lhs
        A B (@dependent_simplex_unprofiled_functor A B) X Y Z g f);

// A decoded strict code collapses that same generic compositor to identity.
assert [A B : Cat]
  (S : τ (@StrictFunctorData A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor
    A B (@strict_functor_carrier A B S) X Y Z g f
  ≡ @id
      (Hom_cat B
        (@fapp0 A B (@strict_functor_carrier A B S) X)
        (@fapp0 A B (@strict_functor_carrier A B S) Z))
      (@strict_functor_compositor_lhs
        A B (@strict_functor_carrier A B S) X Y Z g f);

// Path realization reads the same compositor as an equality with a symmetric
// inverse and keeps the existing higher action.
assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_path A B h x y z q p
  ≡ @fapp1_compositor
      (Path_cat A) (Path_cat B) (@path_map_func A B h)
      x y z q p;

assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_inverse A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_rhs A B h x y z q p)
      (@path_map_compositor_lhs A B h x y z q p));

// If the target fibres are path categories, the dependent component of the
// recursive tetrahedron is itself an equality.
type λ K : Cat, λ E : τ (Catd K), λ B : Grpd,
  λ FF : τ (Functord E (@Const_catd K (Path_cat B))),
  λ x : τ (Obj K), λ u : τ (Obj (Fibre_cat E x)),
  λ y : τ (Obj K), λ v : τ (Obj (Fibre_cat E y)),
  λ p0 : τ (Hom K x y), λ p1 : τ (Hom K x y),
  λ alpha0 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p0)),
  λ alpha1 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p1)),
  λ kappa : τ (Hom (Op_cat (Hom_cat K x y)) p1 p0),
  λ lambda : τ (Obj (Fibre_cat
    (@homd_
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v)
      (@DependentTriangle_catd K E x u y v)
      (@id_funcd
        (Op_cat (Hom_cat K x y))
        (@DependentTriangle_catd K E x u y v))
      p1 alpha1 p0 alpha0)
    kappa)),
    sigma_Snd
      (@dependent_tetrahedron_image
        K E (@Const_catd K (Path_cat B)) FF
        x u y v p0 p1 alpha0 alpha1
        (@dependent_tetrahedron
          K E x u y v p0 p1 alpha0 alpha1 kappa lambda));

// Equality symmetry supplies its inverse without an inverse record.
type λ K : Cat, λ E : τ (Catd K), λ B : Grpd,
  λ FF : τ (Functord E (@Const_catd K (Path_cat B))),
  λ x : τ (Obj K), λ u : τ (Obj (Fibre_cat E x)),
  λ y : τ (Obj K), λ v : τ (Obj (Fibre_cat E y)),
  λ p0 : τ (Hom K x y), λ p1 : τ (Hom K x y),
  λ alpha0 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p0)),
  λ alpha1 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd K E x u y v) p1)),
  λ kappa : τ (Hom (Op_cat (Hom_cat K x y)) p1 p0),
  λ lambda : τ (Obj (Fibre_cat
    (@homd_
      (Op_cat (Hom_cat K x y))
      (@DependentTriangle_catd K E x u y v)
      (@DependentTriangle_catd K E x u y v)
      (@id_funcd
        (Op_cat (Hom_cat K x y))
        (@DependentTriangle_catd K E x u y v))
      p1 alpha1 p0 alpha0)
    kappa)),
    @eq_sym _ _ _
      (sigma_Snd
        (@dependent_tetrahedron_image
          K E (@Const_catd K (Path_cat B)) FF
          x u y v p0 p1 alpha0 alpha1
          (@dependent_tetrahedron
            K E x u y v p0 p1 alpha0 alpha1 kappa lambda)));
