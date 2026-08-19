/*
  Reviewer for the dimension-four flagged acceptance boundary.

  The fourth level is one more PathOut category with recursively derived whole
  map action. Visible data expose faces 0124 and 0134 immediately; one typed
  readable split exposes face 0234 and the retained 1234/top-filler frame.
  The latter is intentionally not flattened without recursive readable views.
*/

require open emdash.emdash3_2_dependent_simplex_dimension4;

assert [C : Cat]
  (x0 : τ (Obj C))
  (e01 : τ (Obj (@DependentSimplex1_cat C x0)))
  (t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)))
  (s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012))) ⊢
  @DependentSimplex4_cat C x0 e01 t012 s0123
  ≡ @PathOut_cat (@DependentSimplex3_cat C x0 e01 t012) s0123;

// The target tetrahedron 0124 is the first projection.
assert [C : Cat]
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
    s0134))) ⊢
  sigma_Fst (@dependent_simplex4_visible
    C x0 e01 t012 t013 t014 s0123 s0124 s0134 alpha01234)
  ≡ @dependent_simplex3 C x0 e01 t012 t014 s0124;

// The base tetrahedron 0134 and final represented component are next.
assert [C : Cat]
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
    s0134))) ⊢
  sigma_Fst (sigma_Snd (@dependent_simplex4_visible
    C x0 e01 t012 t013 t014 s0123 s0124 s0134 alpha01234))
  ≡ s0134;

assert [C : Cat]
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
    s0134))) ⊢
  sigma_Snd (sigma_Snd (@dependent_simplex4_visible
    C x0 e01 t012 t013 t014 s0123 s0124 s0134 alpha01234))
  ≡ alpha01234;

// The endpoint adapter retains a whole cell at literal composition.
assert [C : Cat]
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
    s0134))) ⊢
  @dependent_simplex4_readable_cell
    C x0 e01 t012 t013 t014 s0123 s0124 s0134 alpha01234
  : τ (Obj (Hom_cat
      (Hom_cat (@DependentSimplex2_cat C x0 e01) t012 t014)
      (@comp_fapp0
        (@DependentSimplex2_cat C x0 e01)
        t012 t013 t014 s0134 s0123)
      s0124));

// At visible lower tetrahedra the first split exposes face 0234 and retains
// one final dependent frame.
type λ C : Cat, λ x0 : τ (Obj C),
  λ e01 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ e02 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ e03 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ e04 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ q012 : τ (Hom (@DependentSimplex1_cat C x0) e01 e02),
  λ q013 : τ (Hom (@DependentSimplex1_cat C x0) e01 e03),
  λ q014 : τ (Hom (@DependentSimplex1_cat C x0) e01 e04),
  λ q023 : τ (Hom (@DependentSimplex1_cat C x0) e02 e03),
  λ q024 : τ (Hom (@DependentSimplex1_cat C x0) e02 e04),
  λ q034 : τ (Hom (@DependentSimplex1_cat C x0) e03 e04),
  λ a0123 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e03 q013) q023)),
  λ a0124 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e02 q012 e04 q014) q024)),
  λ a0134 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd (@DependentSimplex1_cat C x0)
      (@Rep_catd (@DependentSimplex1_cat C x0) e01)
      e03 q013 e04 q014) q034)),
  λ alpha01234 : τ (Obj (Fibre_cat
    (@DependentTriangle_catd
      (@DependentSimplex2_cat C x0 e01)
      (@Rep_catd (@DependentSimplex2_cat C x0 e01)
        (@dependent_simplex2 C x0 e01 e02 q012))
      (@dependent_simplex2 C x0 e01 e03 q013)
      (@dependent_simplex_visible_tetrahedron
        C x0 e01 e02 e03 q012 q013 q023 a0123)
      (@dependent_simplex2 C x0 e01 e04 q014)
      (@dependent_simplex_visible_tetrahedron
        C x0 e01 e02 e04 q012 q014 q024 a0124))
    (@dependent_simplex_visible_tetrahedron
      C x0 e01 e03 e04 q013 q014 q034 a0134))),
    sigma_Fst (@dependent_simplex4_visible_readable_cell
      C x0 e01 e02 e03 e04
      q012 q013 q014 q023 q024 q034
      a0123 a0124 a0134 alpha01234);

type λ C : Cat, λ D : Cat, λ F : τ (Functor C D),
  λ x0 : τ (Obj C),
  λ e01 : τ (Obj (@DependentSimplex1_cat C x0)),
  λ t012 : τ (Obj (@DependentSimplex2_cat C x0 e01)),
  λ s0123 : τ (Obj (@DependentSimplex3_cat C x0 e01 t012)),
  λ w0 : τ (Obj (@DependentSimplex4_cat C x0 e01 t012 s0123)),
  λ w1 : τ (Obj (@DependentSimplex4_cat C x0 e01 t012 s0123)),
    @fapp1_func
      (@DependentSimplex4_cat C x0 e01 t012 s0123)
      _
      (@dependent_simplex4_map C D F x0 e01 t012 s0123)
      w0 w1;
