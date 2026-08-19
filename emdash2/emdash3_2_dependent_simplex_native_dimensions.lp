/*
  Native dependent-hom simplex presentations through dimension three.

  The honest recursive classifier is flagged: after choosing the initial
  lower face, the next simplex dimension is an outgoing-path category.

    S0(C)                   = C
    S1(C,x0)                = PathOut_C(x0)
    S2(C,x0,e01)            = PathOut_{S1(C,x0)}(e01)
    S3(C,x0,e01,t012)       = PathOut_{S2(C,x0,e01)}(t012).

  Since PathOut is the Sigma total of a represented `Hom_cat` family, each
  successor exposes the existing `Hom(Sigma)`/`homd_` presentation. Visible
  dimension-two data are three edges and one dependent triangle cell. Visible
  dimension-three data are three lower triangles plus a represented cell; a
  typed endpoint conjugation exposes its fourth face and top filler.

  `pathout_map_func` derives the whole functor action from the existing
  displayed hom action, fixed-base Sigma map, and pullback-total map. Iterating
  it gives whole map action through S3 and leaves every next hom action at the
  generic `fapp1_func` owner. These are flagged classifiers, not yet one global
  category of all n-simplices or an ordinal/dependent equivalence. No rule,
  unifier, Sigma eta, or duplicate simplex semantics is added.
*/

require open emdash.emdash3_2_dependent_simplex_represented_source;

// Whole action of F on outgoing paths from x.
symbol pathout_map_func
  [C D : Cat]
  (F : τ (Functor C D))
  (x : τ (Obj C))
  : τ (Functor
      (@PathOut_cat C x)
      (@PathOut_cat D (@fapp0 C D F x)))
≔ @comp_cat_fapp0
    (@PathOut_cat C x)
    (@Sigma_cat C (@hom_ D C F (@fapp0 C D F x)))
    (@PathOut_cat D (@fapp0 C D F x))
    (@sigma_pullback_total_func
      C D F
      (@Rep_catd D (@fapp0 C D F x)))
    (@sigma_map_func
      C
      (@Rep_catd C x)
      (@hom_ D C F (@fapp0 C D F x))
      (@fapp1_at_transf C D F x));

// Dimension zero: the ambient category itself.
symbol DependentSimplex0_cat (C : Cat) : Cat
≔ C;

// Dimension one after fixing the initial vertex x0.
symbol DependentSimplex1_cat
  [C : Cat]
  (x0 : τ (Obj C))
  : Cat
≔ @PathOut_cat C x0;

// Dimension two after fixing the initial edge e01.
symbol DependentSimplex2_cat
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  : Cat
≔ @PathOut_cat (@DependentSimplex1_cat C x0) e01;

// Dimension three after fixing the initial triangle t012.
symbol DependentSimplex3_cat
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  : Cat
≔ @PathOut_cat (@DependentSimplex2_cat C x0 e01) t012;

// Whole map action in dimension zero.
symbol dependent_simplex0_map
  [C D : Cat]
  (F : τ (Functor C D))
  : τ (Functor (@DependentSimplex0_cat C) (@DependentSimplex0_cat D))
≔ F;

// Whole map action on fixed-source edges.
symbol dependent_simplex1_map
  [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C))
  : τ (Functor
      (@DependentSimplex1_cat C x0)
      (@DependentSimplex1_cat D (@fapp0 C D F x0)))
≔ @pathout_map_func C D F x0;

// Whole map action on triangles at a fixed initial edge.
symbol dependent_simplex2_map
  [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  : τ (Functor
      (@DependentSimplex2_cat C x0 e01)
      (@DependentSimplex2_cat
        D
        (@fapp0 C D F x0)
        (@fapp0
          (@DependentSimplex1_cat C x0)
          (@DependentSimplex1_cat D (@fapp0 C D F x0))
          (@dependent_simplex1_map C D F x0)
          e01)))
≔ @pathout_map_func
    (@DependentSimplex1_cat C x0)
    (@DependentSimplex1_cat D (@fapp0 C D F x0))
    (@dependent_simplex1_map C D F x0)
    e01;

// Whole map action on tetrahedra at a fixed initial triangle.
symbol dependent_simplex3_map
  [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  : τ (Functor
      (@DependentSimplex3_cat C x0 e01 t012)
      (@DependentSimplex3_cat
        D
        (@fapp0 C D F x0)
        (@fapp0
          (@DependentSimplex1_cat C x0)
          (@DependentSimplex1_cat D (@fapp0 C D F x0))
          (@dependent_simplex1_map C D F x0)
          e01)
        (@fapp0
          (@DependentSimplex2_cat C x0 e01)
          _
          (@dependent_simplex2_map C D F x0 e01)
          t012)))
≔ @pathout_map_func
    (@DependentSimplex2_cat C x0 e01)
    _
    (@dependent_simplex2_map C D F x0 e01)
    t012;

// Constructor-visible edge from x0 to x1.
symbol dependent_simplex1
  [C : Cat]
  (x0 x1 : τ (Obj C))
  (p01 : τ (Hom C x0 x1))
  : τ (Obj (@DependentSimplex1_cat C x0))
≔ @pathout_obj C x0 x1 p01;

// Constructor-visible triangle from e01 to e02.
symbol dependent_simplex2
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 e02 : τ (Obj (@DependentSimplex1_cat C x0)))
  (q012 : τ (Hom (@DependentSimplex1_cat C x0) e01 e02))
  : τ (Obj (@DependentSimplex2_cat C x0 e01))
≔ @pathout_obj
    (@DependentSimplex1_cat C x0)
    e01 e02 q012;

// Constructor-visible tetrahedron from t012 to t013.
symbol dependent_simplex3
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 t013 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (theta : τ (Hom (@DependentSimplex2_cat C x0 e01) t012 t013))
  : τ (Obj (@DependentSimplex3_cat C x0 e01 t012))
≔ @pathout_obj
    (@DependentSimplex2_cat C x0 e01)
    t012 t013 theta;

// Triangle face with all three underlying C-edges visible.
symbol dependent_simplex_visible_triangle
  [C : Cat]
  (x0 xi xj : τ (Obj C))
  (p0i : τ (Hom C x0 xi))
  (p0j : τ (Hom C x0 xj))
  (pij : τ (Hom C xi xj))
  (alpha : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) xi p0i xj p0j)
    pij)))
  : τ (Hom
      (@DependentSimplex1_cat C x0)
      (@dependent_simplex1 C x0 xi p0i)
      (@dependent_simplex1 C x0 xj p0j))
≔ @dependent_triangle
    C (@Rep_catd C x0)
    xi p0i xj p0j pij alpha;

// Fully visible dimension-two object: edges 01, 02, 12 and filler alpha012.
symbol dependent_simplex2_visible
  [C : Cat]
  (x0 x1 x2 : τ (Obj C))
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p12 : τ (Hom C x1 x2))
  (alpha012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      C (@Rep_catd C x0) x1 p01 x2 p02)
    p12)))
  : τ (Obj (@DependentSimplex2_cat
      C x0
      (@dependent_simplex1 C x0 x1 p01)))
≔ @dependent_simplex2
    C x0
    (@dependent_simplex1 C x0 x1 p01)
    (@dependent_simplex1 C x0 x2 p02)
    (@dependent_simplex_visible_triangle
      C x0 x1 x2 p01 p02 p12 alpha012);

// Fully visible dimension-three object before splitting its final cell.
symbol dependent_simplex3_visible
  [C : Cat]
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
    q023)))
  : τ (Obj (@DependentSimplex3_cat
      C x0 e01
      (@dependent_simplex2 C x0 e01 e02 q012)))
≔ @dependent_simplex3
    C x0 e01
    (@dependent_simplex2 C x0 e01 e02 q012)
    (@dependent_simplex2 C x0 e01 e03 q013)
    (@dependent_triangle
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e03 q013 q023 alpha0123);

// Readable final cell: move the stable represented source to q023 o q012.
symbol dependent_simplex3_readable_cell
  [Z : Cat]
  [e01 e02 e03 : τ (Obj Z)]
  (q012 : τ (Hom Z e01 e02))
  (q013 : τ (Hom Z e01 e03))
  (q023 : τ (Hom Z e02 e03))
  (alpha0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      Z (@Rep_catd Z e01) e02 q012 e03 q013)
    q023)))
  : τ (Obj (Hom_cat
      (Hom_cat Z e01 e03)
      (@comp_fapp0 Z e01 e02 e03 q023 q012)
      q013))
≔ @comp_fapp0
    (Hom_cat Z e01 e03)
    (@comp_fapp0 Z e01 e02 e03 q023 q012)
    (@hom_postcomp_fapp0
      Z Z (@id_func Z) e01 e02 e03 q023 q012)
    q013
    alpha0123
    (@path_to_hom
      (Hom_cat Z e01 e03)
      (@comp_fapp0 Z e01 e02 e03 q023 q012)
      (@hom_postcomp_fapp0
        Z Z (@id_func Z) e01 e02 e03 q023 q012)
      (@eq_sym
        (Hom Z e01 e03)
        (@hom_postcomp_fapp0
          Z Z (@id_func Z) e01 e02 e03 q023 q012)
        (@comp_fapp0 Z e01 e02 e03 q023 q012)
        (@path_pseudo_laxity_postcomp_comp_path
          Z Z (@id_func Z) e01 e02 e03 q023 q012)));

// C-level specialization whose lower faces remain constructor-visible. Its
// Hom(Sigma) result therefore admits the final face/filler projections.
symbol dependent_simplex3_visible_readable_cell
  [C : Cat]
  (x0 x1 x2 x3 : τ (Obj C))
  (p01 : τ (Hom C x0 x1))
  (p02 : τ (Hom C x0 x2))
  (p03 : τ (Hom C x0 x3))
  (p12 : τ (Hom C x1 x2))
  (p13 : τ (Hom C x1 x3))
  (p23 : τ (Hom C x2 x3))
  (a012 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x1 p01 x2 p02) p12)))
  (a013 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x1 p01 x3 p03) p13)))
  (a023 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd C (@Rep_catd C x0) x2 p02 x3 p03) p23)))
  (alpha0123 : τ (Obj (Fibre_cat
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
      C x0 x2 x3 p02 p03 p23 a023))))
  : τ (Obj (Hom_cat
      (Hom_cat
        (@DependentSimplex1_cat C x0)
        (@dependent_simplex1 C x0 x1 p01)
        (@dependent_simplex1 C x0 x3 p03))
      (@comp_fapp0
        (@DependentSimplex1_cat C x0)
        (@dependent_simplex1 C x0 x1 p01)
        (@dependent_simplex1 C x0 x2 p02)
        (@dependent_simplex1 C x0 x3 p03)
        (@dependent_simplex_visible_triangle
          C x0 x2 x3 p02 p03 p23 a023)
        (@dependent_simplex_visible_triangle
          C x0 x1 x2 p01 p02 p12 a012))
      (@dependent_simplex_visible_triangle
        C x0 x1 x3 p01 p03 p13 a013)))
≔ @dependent_simplex3_readable_cell
    (@DependentSimplex1_cat C x0)
    (@dependent_simplex1 C x0 x1 p01)
    (@dependent_simplex1 C x0 x2 p02)
    (@dependent_simplex1 C x0 x3 p03)
    (@dependent_simplex_visible_triangle
      C x0 x1 x2 p01 p02 p12 a012)
    (@dependent_simplex_visible_triangle
      C x0 x1 x3 p01 p03 p13 a013)
    (@dependent_simplex_visible_triangle
      C x0 x2 x3 p02 p03 p23 a023)
    alpha0123;
