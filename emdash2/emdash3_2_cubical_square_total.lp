/*
  Emdash v3.2: a fixed-boundary cubical square total and its next action.

  The fixed-endpoint homdc_ classifier is totalized first in its
  contravariant b coordinate and then in its covariant a coordinate. Objects
  are constructor-visible triples (a,(b,alpha)); the four variance-correct
  line observations are whole. An arrow between two such objects has the two
  endpoint squares and four projected side faces.

  The source and target vertical edges u,v are fixed parameters of this first
  bounded total. Consequently their two side faces are degenerate identities;
  full nondegenerate endpoint variation remains gated by functoriality of
  homd_int in its displayed-functor parameter. The bottom face deliberately
  remains a Pi-section action over the stable Sigma-projection pullback rather
  than being forced through a false strict-constant conversion.
*/

require open emdash.emdash3_2_cubical_dependent_hom;

// Whole family of first projections from a varying Sigma total.
injective symbol sigma_proj1_family_funcd
  [K A : Cat]
  (G : τ (Functor K (Catd_cat A)))
  : τ (Functord
      (@comp_cat_fapp0
        K (Catd_cat A) Cat_cat
        (@Sigma_func A)
        G)
      (@Const_catd K A));

// The component at k is the ordinary first projection of Sigma(G[k]).
rule @tapp0_fapp0
      $K Cat_cat _ _ $k
      (@sigma_proj1_family_funcd $K $A $G)
  ↪ @Sigma_proj1_func
      $A
      (@fapp0 $K (@Catd_cat $A) $G $k);

// Its displayed action sends a constructor-visible total arrow (q,beta) to
// the base arrow q. This is the varying-family analogue of the ordinary
// Sigma_proj1_func arrow beta; all inferred slots are reconstructible from
// the displayed-functor head and visible dependent pair.
rule @fdapp1_int_hom_fapp0
      _
      _
      _
      (@sigma_proj1_family_funcd _ _ _)
      _
      _
      _
      (Struct_sigma _ _)
      (Struct_sigma _ _)
      (Struct_sigma $q _)
  ↪ $q;

// Pointwise opposite retains the same base arrow under the opposite Hom
// orientation. The separate stable Op_funcd head requires this generic
// specialization; no cubical endpoint or dimension appears in the rule.
rule @fdapp1_int_hom_fapp0
      _
      _
      _
      (@Op_funcd _ _ _ (@sigma_proj1_family_funcd _ _ _))
      _
      _
      _
      (Struct_sigma _ _)
      (Struct_sigma _ _)
      (Struct_sigma $q _)
  ↪ $q;

// At a, totalize the b-indexed filler family.
symbol homdc_inner_total_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Functor (Hom_cat K1 x1 y1) Cat_cat)
≔ @comp_cat_fapp0
    (Hom_cat K1 x1 y1)
    (Catd_cat (Op_cat (Hom_cat K2 x2 y2)))
    Cat_cat
    (@Sigma_func (Op_cat (Hom_cat K2 x2 y2)))
    (@homdc_ K1 K2 E x1 y1 x2 y2 u v);

// Fixed vertical boundary; objects are (a,(b,alpha)).
symbol homdc_square_cat
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : Cat
≔ @Sigma_cat
    (Hom_cat K1 x1 y1)
    (@homdc_inner_total_func
      K1 K2 E x1 y1 x2 y2 u v);

// Variance-correct target family of the inner face section.
symbol homdc_square_bottom_catd
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Catd
      (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v))
≔ @Sigma_proj1_pullback_catd
    (Hom_cat K1 x1 y1)
    (@homdc_inner_total_func K1 K2 E x1 y1 x2 y2 u v)
    (@Const_catd
      (Hom_cat K1 x1 y1)
      (Op_cat (Hom_cat K2 x2 y2)));

// Outer/first-coordinate line face.
symbol homdc_square_top_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Functor
      (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
      (Hom_cat K1 x1 y1))
≔ @Sigma_proj1_func
    (Hom_cat K1 x1 y1)
    (@homdc_inner_total_func
      K1 K2 E x1 y1 x2 y2 u v);

// Fixed source and target vertical line faces. They remain whole constant
// functors; their action produces the two degenerate side faces in the first
// bounded cube test.
symbol homdc_square_left_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Functor
      (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
        x2))
≔ @Const_func
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Fibre_cat
      (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
      x2)
    u;

symbol homdc_square_right_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Functor
      (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
      (Fibre_cat
        (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
        y2))
≔ @Const_func
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Fibre_cat
      (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
      y2)
    v;

// Inner/second-coordinate line face. Its target is opposite because b is the
// contravariant coordinate of the selected source-to-target hom family.
symbol homdc_square_bottom_sec
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  : τ (Obj
      (@Pi_cat
        (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_bottom_catd
          K1 K2 E x1 y1 x2 y2 u v)))
≔ @sigma_functord_sec
    (Hom_cat K1 x1 y1)
    (@homdc_inner_total_func
      K1 K2 E x1 y1 x2 y2 u v)
    (@Const_catd
      (Hom_cat K1 x1 y1)
      (Op_cat (Hom_cat K2 x2 y2)))
    (@sigma_proj1_family_funcd
      (Hom_cat K1 x1 y1)
      (Op_cat (Hom_cat K2 x2 y2))
      (@homdc_ K1 K2 E x1 y1 x2 y2 u v));

// Constructor-visible square object.
symbol homdc_square_obj
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2))
  (alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b)))
  : τ (Obj
      (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v))
≔ Struct_sigma a (Struct_sigma b alpha);

// A next-hom object theta between two square objects has six faces: its two
// ordinary endpoints plus the images below under the four whole line faces.
symbol homdc_cube_top_face
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  [a a' : τ (Hom K1 x1 y1)]
  [b b' : τ (Hom K2 x2 y2)]
  [alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))]
  [beta : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a' b'))]
  (theta : τ (Hom
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)))
  : τ (Hom (Hom_cat K1 x1 y1) a a')
≔ @fapp1_fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Hom_cat K1 x1 y1)
    (@homdc_square_top_func K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)
    theta;

symbol homdc_cube_bottom_face
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  [a a' : τ (Hom K1 x1 y1)]
  [b b' : τ (Hom K2 x2 y2)]
  [alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))]
  [beta : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a' b'))]
  (theta : τ (Hom
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)))
  : τ (Hom
      (Fibre_cat
        (@homdc_square_bottom_catd
          K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_obj
          K1 K2 E x1 y1 x2 y2 u v a' b' beta))
      (@piapp1_src_obj
        (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_bottom_catd
          K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_bottom_sec
          K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_obj
          K1 K2 E x1 y1 x2 y2 u v a b alpha)
        (@homdc_square_obj
          K1 K2 E x1 y1 x2 y2 u v a' b' beta)
        theta)
      (@piapp0
        (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_bottom_catd
          K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_bottom_sec
          K1 K2 E x1 y1 x2 y2 u v)
        (@homdc_square_obj
          K1 K2 E x1 y1 x2 y2 u v a' b' beta)))
≔ @piapp1_fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_bottom_catd
      K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_bottom_sec K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)
    theta;

symbol homdc_cube_left_face
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  [a a' : τ (Hom K1 x1 y1)]
  [b b' : τ (Hom K2 x2 y2)]
  [alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))]
  [beta : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a' b'))]
  (theta : τ (Hom
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)))
  : τ (Hom
      (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)
      u u)
≔ @fapp1_fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)
    (@homdc_square_left_func K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)
    theta;

symbol homdc_cube_right_face
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  [a a' : τ (Hom K1 x1 y1)]
  [b b' : τ (Hom K2 x2 y2)]
  [alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))]
  [beta : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a' b'))]
  (theta : τ (Hom
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)))
  : τ (Hom
      (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)
      v v)
≔ @fapp1_fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)
    (@homdc_square_right_func K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta)
    theta;
