/*
  Reviewer for flagged native dependent simplices through dimension three.

  Iterated PathOut categories expose the existing Sigma/homd recursion. Whole
  map action is derived from the generic functor action, visible dimensions
  two and three expose every boundary layer, and the final stable represented
  endpoint is moved propositionally before its 123-face/filler projection.
*/

require open emdash.emdash3_2_dependent_simplex_native_dimensions;

// A visible outgoing arrow maps by the ordinary hom action of F.
assert [C D : Cat]
  (F : τ (Functor C D))
  [x y : τ (Obj C)]
  (p : τ (Hom C x y)) ⊢
  @fapp0
    (@PathOut_cat C x)
    (@PathOut_cat D (@fapp0 C D F x))
    (@pathout_map_func C D F x)
    (@pathout_obj C x y p)
  ≡ @pathout_obj
      D
      (@fapp0 C D F x)
      (@fapp0 C D F y)
      (@fapp1_fapp0 C D F x y p);

// The native levels are literally the iterated PathOut/Sigma tower.
assert [C : Cat] (x0 : τ (Obj C)) ⊢
  @DependentSimplex1_cat C x0
  ≡ @PathOut_cat C x0;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0))) ⊢
  @DependentSimplex2_cat C x0 e01
  ≡ @PathOut_cat (@DependentSimplex1_cat C x0) e01;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01))) ⊢
  @DependentSimplex3_cat C x0 e01 t012
  ≡ @PathOut_cat (@DependentSimplex2_cat C x0 e01) t012;

// Dimension two exposes edge 02, edge 12, and the triangle filler; edge 01 is
// the flag indexing the classifier.
assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  sigma_Fst (@dependent_simplex2_visible
    C x0 x1 x2 p01 p02 p12 alpha012)
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
  sigma_Fst (sigma_Snd (@dependent_simplex2_visible
    C x0 x1 x2 p01 p02 p12 alpha012))
  ≡ p12;

assert [C : Cat]
  [x0 x1 x2 : τ (Obj C)]
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12))) ⊢
  sigma_Snd (sigma_Snd (@dependent_simplex2_visible
    C x0 x1 x2 p01 p02 p12 alpha012))
  ≡ alpha012;

// Dimension three exposes faces 013 and 023 immediately; face 012 is its
// classifier flag and alpha0123 is the stable represented final face/filler.
assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 e02 e03 : τ (Obj (@DependentSimplex1_cat C x0)))
  (q012 : τ (Hom (@DependentSimplex1_cat C x0) e01 e02))
  (q013 : τ (Hom (@DependentSimplex1_cat C x0) e01 e03))
  (q023 : τ (Hom (@DependentSimplex1_cat C x0) e02 e03))
  (alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e03 q013)
    q023))) ⊢
  sigma_Fst (@dependent_simplex3_visible
    C x0 e01 e02 e03 q012 q013 q023 alpha0123)
  ≡ @dependent_simplex2 C x0 e01 e03 q013;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 e02 e03 : τ (Obj (@DependentSimplex1_cat C x0)))
  (q012 : τ (Hom (@DependentSimplex1_cat C x0) e01 e02))
  (q013 : τ (Hom (@DependentSimplex1_cat C x0) e01 e03))
  (q023 : τ (Hom (@DependentSimplex1_cat C x0) e02 e03))
  (alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e03 q013)
    q023))) ⊢
  sigma_Fst (sigma_Snd (@dependent_simplex3_visible
    C x0 e01 e02 e03 q012 q013 q023 alpha0123))
  ≡ q023;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 e02 e03 : τ (Obj (@DependentSimplex1_cat C x0)))
  (q012 : τ (Hom (@DependentSimplex1_cat C x0) e01 e02))
  (q013 : τ (Hom (@DependentSimplex1_cat C x0) e01 e03))
  (q023 : τ (Hom (@DependentSimplex1_cat C x0) e02 e03))
  (alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e03 q013)
    q023))) ⊢
  sigma_Snd (sigma_Snd (@dependent_simplex3_visible
    C x0 e01 e02 e03 q012 q013 q023 alpha0123))
  ≡ alpha0123;

// The typed endpoint adapter exposes the fourth face/filler pair at literal
// composition without selecting a new runtime normal form.
assert [Z : Cat]
  [e01 e02 e03 : τ (Obj Z)]
  (q012 : τ (Hom Z e01 e02))
  (q013 : τ (Hom Z e01 e03))
  (q023 : τ (Hom Z e02 e03))
  (alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      Z (@Rep_catd Z e01) e02 q012 e03 q013)
    q023))) ⊢
  @dependent_simplex3_readable_cell Z e01 e02 e03 q012 q013 q023 alpha0123
  : τ (Obj (Hom_cat
      (Hom_cat Z e01 e03)
      (@comp_fapp0 Z e01 e02 e03 q023 q012)
      q013));

// With every lower face constructor visible, that readable cell splits into
// the 123 face and the top dependent filler.
type λ C : Cat,
  λ x0 : τ (Obj C), λ x1 : τ (Obj C),
  λ x2 : τ (Obj C), λ x3 : τ (Obj C),
  λ p01 : τ (Hom C x0 x1), λ p02 : τ (Hom C x0 x2),
  λ p03 : τ (Hom C x0 x3), λ p12 : τ (Hom C x1 x2),
  λ p13 : τ (Hom C x1 x3), λ p23 : τ (Hom C x2 x3),
  λ a012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x1 p01 x2 p02) p12)),
  λ a013 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x1 p01 x3 p03) p13)),
  λ a023 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x2 p02 x3 p03) p23)),
  λ alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd
        (@DependentSimplex1_cat C x0)
        (@dependent_simplex1 C x0 x1 p01))
      (@dependent_simplex1 C x0 x2 p02)
      (@dependent_simplex_visible_triangle
        C x0 x1 x2 p01 p02 p12 a012)
      (@dependent_simplex1 C x0 x3 p03)
      (@dependent_simplex_visible_triangle
        C x0 x1 x3 p01 p03 p13 a013))
    (@dependent_simplex_visible_triangle
      C x0 x2 x3 p02 p03 p23 a023))),
    sigma_Fst
      (@dependent_simplex3_visible_readable_cell
        C x0 x1 x2 x3
        p01 p02 p03 p12 p13 p23
        a012 a013 a023 alpha0123);

type λ C : Cat,
  λ x0 : τ (Obj C), λ x1 : τ (Obj C),
  λ x2 : τ (Obj C), λ x3 : τ (Obj C),
  λ p01 : τ (Hom C x0 x1), λ p02 : τ (Hom C x0 x2),
  λ p03 : τ (Hom C x0 x3), λ p12 : τ (Hom C x1 x2),
  λ p13 : τ (Hom C x1 x3), λ p23 : τ (Hom C x2 x3),
  λ a012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x1 p01 x2 p02) p12)),
  λ a013 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x1 p01 x3 p03) p13)),
  λ a023 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x2 p02 x3 p03) p23)),
  λ alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd
        (@DependentSimplex1_cat C x0)
        (@dependent_simplex1 C x0 x1 p01))
      (@dependent_simplex1 C x0 x2 p02)
      (@dependent_simplex_visible_triangle
        C x0 x1 x2 p01 p02 p12 a012)
      (@dependent_simplex1 C x0 x3 p03)
      (@dependent_simplex_visible_triangle
        C x0 x1 x3 p01 p03 p13 a013))
    (@dependent_simplex_visible_triangle
      C x0 x2 x3 p02 p03 p23 a023))),
    sigma_Snd
      (@dependent_simplex3_visible_readable_cell
        C x0 x1 x2 x3
        p01 p02 p03 p12 p13 p23
        a012 a013 a023 alpha0123);

// Whole dimension-three action remains iterable at another hom level.
type λ C : Cat, λ D : Cat, λ F : τ (Functor C D),
  λ x0 : τ (Obj C),
  λ e01 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)),
  λ s0 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)),
  λ s1 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)),
    @fapp1_func
      (@DependentSimplex3_cat C x0 e01 t012)
      _
      (@dependent_simplex3_map C D F x0 e01 t012)
      s0 s1;
