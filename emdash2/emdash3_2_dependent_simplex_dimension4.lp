/*
  Dimension-four acceptance boundary for the flagged dependent-simplex tower.

  The fourth classifier is one more outgoing-path category. A visible object
  carries the flagged face 0123, target face 0124, base face 0134, and one
  represented dependent component. The existing readable-cell adapter moves
  that component to literal composition. At constructor-visible lower
  tetrahedra, Hom(Sigma) then exposes face 0234 and one residual dependent
  frame.

  That residual is intentionally not flattened here into face 1234 plus the
  top filler. A focused full-visibility probe shows that its lower tetrahedra
  still carry formal represented endpoints; recursively transporting their
  readable views is the requirement extracted for the later code/decoder.
  This module adds no dimension-specific eta, endpoint rewrite, rule, unifier,
  or global all-simplex category. Whole map action and its next hom action are
  inherited by one more iteration of `pathout_map_func`.
*/

require open emdash.emdash3_2_dependent_simplex_native_dimensions;

// Dimension four after fixing the initial tetrahedron s0123.
symbol DependentSimplex4_cat
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)))
  : Cat
≔ @PathOut_cat (@DependentSimplex3_cat C x0 e01 t012) s0123;

// Whole ordinary-functor action on the fourth flagged level.
symbol dependent_simplex4_map
  [C D : Cat]
  (F : τ (Functor C D))
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)))
  : τ (Functor
      (@DependentSimplex4_cat C x0 e01 t012 s0123)
      (@DependentSimplex4_cat
        D
        (@fapp0 C D F x0)
        (@fapp0 _ _ (@dependent_simplex1_map C D F x0) e01)
        (@fapp0 _ _ (@dependent_simplex2_map C D F x0 e01) t012)
        (@fapp0 _ _ (@dependent_simplex3_map C D F x0 e01 t012) s0123)))
≔ @pathout_map_func
    (@DependentSimplex3_cat C x0 e01 t012)
    _
    (@dependent_simplex3_map C D F x0 e01 t012)
    s0123;

// Constructor-visible fourth-level object from two tetrahedra and one cell.
symbol dependent_simplex4
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 s0124 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)))
  (omega : τ (Hom (@DependentSimplex3_cat C x0 e01 t012) s0123 s0124))
  : τ (Obj (@DependentSimplex4_cat C x0 e01 t012 s0123))
≔ @pathout_obj
    (@DependentSimplex3_cat C x0 e01 t012)
    s0123 s0124 omega;

// Constructor-visible tetrahedron face in the second native level.
symbol dependent_simplex_visible_tetrahedron
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
  : τ (Hom
      (@DependentSimplex2_cat C x0 e01)
      (@dependent_simplex2 C x0 e01 e02 q012)
      (@dependent_simplex2 C x0 e01 e03 q013))
≔ @dependent_triangle
    (@DependentSimplex1_cat C x0)
    (@Rep_catd (@DependentSimplex1_cat C x0) e01)
    e02 q012 e03 q013 q023 alpha0123;

// Visible fourth-level object before normalizing its final represented cell.
symbol dependent_simplex4_visible
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 t013 t014 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Hom (@DependentSimplex2_cat C x0 e01) t012 t013))
  (s0124 : τ (Hom (@DependentSimplex2_cat C x0 e01) t012 t014))
  (s0134 : τ (Hom (@DependentSimplex2_cat C x0 e01) t013 t014))
  (alpha01234 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex2_cat C x0 e01)
      (@Rep_catd (@DependentSimplex2_cat C x0 e01) t012)
      t013 s0123 t014 s0124)
    s0134)))
  : τ (Obj (@DependentSimplex4_cat
      C x0 e01 t012
      (@dependent_simplex3 C x0 e01 t012 t013 s0123)))
≔ @dependent_simplex4
    C x0 e01 t012
    (@dependent_simplex3 C x0 e01 t012 t013 s0123)
    (@dependent_simplex3 C x0 e01 t012 t014 s0124)
    (@dependent_triangle
      (@DependentSimplex2_cat C x0 e01)
      (@Rep_catd (@DependentSimplex2_cat C x0 e01) t012)
      t013 s0123 t014 s0124 s0134 alpha01234);

// First readable split at the literal composite s0134 o s0123.
symbol dependent_simplex4_readable_cell
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 t013 t014 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Hom (@DependentSimplex2_cat C x0 e01) t012 t013))
  (s0124 : τ (Hom (@DependentSimplex2_cat C x0 e01) t012 t014))
  (s0134 : τ (Hom (@DependentSimplex2_cat C x0 e01) t013 t014))
  (alpha01234 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex2_cat C x0 e01)
      (@Rep_catd (@DependentSimplex2_cat C x0 e01) t012)
      t013 s0123 t014 s0124)
    s0134)))
  : τ (Obj (Hom_cat
      (Hom_cat (@DependentSimplex2_cat C x0 e01) t012 t014)
      (@comp_fapp0
        (@DependentSimplex2_cat C x0 e01)
        t012 t013 t014 s0134 s0123)
      s0124))
≔ @dependent_simplex3_readable_cell
    (@DependentSimplex2_cat C x0 e01)
    t012 t013 t014
    s0123 s0124 s0134 alpha01234;

// Constructor-visible specialization. Its first Sigma projection is face
// 0234; its second projection is the retained 1234/top-filler frame.
symbol dependent_simplex4_visible_readable_cell
  [C : Cat]
  (x0 : τ (Obj C))
  (e01 e02 e03 e04 : τ (Obj (@DependentSimplex1_cat C x0)))
  (q012 : τ (Hom (@DependentSimplex1_cat C x0) e01 e02))
  (q013 : τ (Hom (@DependentSimplex1_cat C x0) e01 e03))
  (q014 : τ (Hom (@DependentSimplex1_cat C x0) e01 e04))
  (q023 : τ (Hom (@DependentSimplex1_cat C x0) e02 e03))
  (q024 : τ (Hom (@DependentSimplex1_cat C x0) e02 e04))
  (q034 : τ (Hom (@DependentSimplex1_cat C x0) e03 e04))
  (a0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e03 q013)
    q023)))
  (a0124 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e04 q014)
    q024)))
  (a0134 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e03 q013 e04 q014)
    q034)))
  (alpha01234 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex2_cat C x0 e01)
      (@Rep_catd
        (@DependentSimplex2_cat C x0 e01)
        (@dependent_simplex2 C x0 e01 e02 q012))
      (@dependent_simplex2 C x0 e01 e03 q013)
      (@dependent_simplex_visible_tetrahedron
        C x0 e01 e02 e03 q012 q013 q023 a0123)
      (@dependent_simplex2 C x0 e01 e04 q014)
      (@dependent_simplex_visible_tetrahedron
        C x0 e01 e02 e04 q012 q014 q024 a0124))
    (@dependent_simplex_visible_tetrahedron
      C x0 e01 e03 e04 q013 q014 q034 a0134))))
  : τ (Obj (Hom_cat
      (Hom_cat
        (@DependentSimplex2_cat C x0 e01)
        (@dependent_simplex2 C x0 e01 e02 q012)
        (@dependent_simplex2 C x0 e01 e04 q014))
      (@comp_fapp0
        (@DependentSimplex2_cat C x0 e01)
        (@dependent_simplex2 C x0 e01 e02 q012)
        (@dependent_simplex2 C x0 e01 e03 q013)
        (@dependent_simplex2 C x0 e01 e04 q014)
        (@dependent_simplex_visible_tetrahedron
          C x0 e01 e03 e04 q013 q014 q034 a0134)
        (@dependent_simplex_visible_tetrahedron
          C x0 e01 e02 e03 q012 q013 q023 a0123))
      (@dependent_simplex_visible_tetrahedron
        C x0 e01 e02 e04 q012 q014 q024 a0124)))
≔ @dependent_simplex4_readable_cell
    C x0 e01
    (@dependent_simplex2 C x0 e01 e02 q012)
    (@dependent_simplex2 C x0 e01 e03 q013)
    (@dependent_simplex2 C x0 e01 e04 q014)
    (@dependent_simplex_visible_tetrahedron
      C x0 e01 e02 e03 q012 q013 q023 a0123)
    (@dependent_simplex_visible_tetrahedron
      C x0 e01 e02 e04 q012 q014 q024 a0124)
    (@dependent_simplex_visible_tetrahedron
      C x0 e01 e03 e04 q013 q014 q034 a0134)
    alpha01234;
