/*
  Emdash v3.2: a fixed-boundary cubical square total and its next action.

  The fixed-endpoint homdc_ classifier is totalized first in its
  contravariant b coordinate and then in its covariant a coordinate. Objects
  are constructor-visible triples (a,(b,alpha)); the four variance-correct
  line observations are whole. An arrow between two such objects has the two
  endpoint squares and four projected side faces.

  The source and target vertical edges u,v are fixed parameters of this first
  bounded total. Consequently their two side faces are degenerate identities.
  The later `emdash3_2_cubical_internalization` module now supplies full
  endpoint variation by applying the existing `homd_int` to the pointwise
  opposite inner edge total; no parameterized-hom primitive is required. The
  bottom face here deliberately remains a Pi-section action over the stable
  Sigma-projection pullback rather than being forced through a false
  strict-constant conversion.
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

// The same base-preservation observation in pointwise opposite fibres.
rule @fdapp1_int_hom_fapp0 _ _ _
      (@Op_funcd $K _ _ (@sigma_proj1_family_funcd $K $A $D))
      $x $y $p (Struct_sigma $a _) (Struct_sigma $b _)
      (@fdapp1_int_hom_fapp0 _ _ _
        (@Op_funcd $K _ _
          (@comp_prod_fapp1_fapp0 Cat_cat _ _ _
            (Struct_sigma $E (@Sigma_func $A))
            (Struct_sigma $D (@Sigma_func $A))
            (Struct_sigma _ (@id (Functor_cat (@Catd_cat $A) Cat_cat) (@Sigma_func $A)))))
        $x $y $p (Struct_sigma $a $u) (Struct_sigma $b $v) $alpha)
  ↪ @fdapp1_int_hom_fapp0
      $K (@Op_catd $K (@comp_cat_fapp0 $K (@Catd_cat $A) Cat_cat (@Sigma_func $A) $E))
      (@Const_catd $K (Op_cat $A))
      (@Op_funcd $K (@comp_cat_fapp0 $K (@Catd_cat $A) Cat_cat (@Sigma_func $A) $E)
        (@Const_catd $K $A) (@sigma_proj1_family_funcd $K $A $E))
      $x $y $p (Struct_sigma $a $u) (Struct_sigma $b $v) $alpha;

// Base observation after family-natural total base change.
// The outer displayed base may differ: only the inner B-coordinate is observed.
rule @fdapp1_int_hom_fapp0 _ _ _
      (@Op_funcd _ _ _ (@sigma_proj1_family_funcd _ $B _))
      _ _ _
      (Struct_sigma (@fapp0 $A $B $G $a) _)
      (Struct_sigma (@fapp0 $A $B $G $b) _)
      (@fdapp1_int_hom_fapp0 _ _ _
        (@Op_funcd $K _ _
          (@comp_prod_fapp1_fapp0 Cat_cat _ _ _
            (Struct_sigma $H _)
            (Struct_sigma $H _)
            (Struct_sigma (@id (Functor_cat $K (@Catd_cat $B)) $H)
              (@sigma_pullback_total_transf $A $B $G))))
        $x $y $p (Struct_sigma $a $u) (Struct_sigma $b $v) $alpha)
  ↪ @fapp1_fapp0 (Op_cat $A) (Op_cat $B) (@Op_func $A $B $G) $a $b
      (@fdapp1_int_hom_fapp0
        $K
        (@Op_catd $K (@comp_cat_fapp0 $K (@Catd_cat $A) Cat_cat (@Sigma_func $A)
          (@comp_cat_fapp0 $K (@Catd_cat $B) (@Catd_cat $A) (@Pullback_catd_func $A $B $G) $H)))
        (@Const_catd $K (Op_cat $A))
        (@Op_funcd $K
          (@comp_cat_fapp0 $K (@Catd_cat $A) Cat_cat (@Sigma_func $A)
            (@comp_cat_fapp0 $K (@Catd_cat $B) (@Catd_cat $A) (@Pullback_catd_func $A $B $G) $H))
          (@Const_catd $K $A)
          (@sigma_proj1_family_funcd $K $A
            (@comp_cat_fapp0 $K (@Catd_cat $B) (@Catd_cat $A) (@Pullback_catd_func $A $B $G) $H)))
        $x $y $p (Struct_sigma $a $u) (Struct_sigma $b $v) $alpha);

// Reindex the canonical opposite Sigma projection, retaining the original
// identity reframe. The side condition checks that reframe's source family.
unif_rule @fapp1_fapp0 _ _ (@Pullback_catd_func $A $B $F) $E0 _
    (@comp_fapp0 (@Catd_cat $B) $E0 _ _
      (@Op_funcd $B _ _ (@sigma_proj1_family_funcd $B $I $G))
      (@id (@Catd_cat $B) $E0))
  ≡ @Op_funcd $A _ _
      (@sigma_proj1_family_funcd $A $I
        (@comp_fapp0 Cat_cat $A $B (@Catd_cat $I) $G $F))
  ↪ [ $E0 ≡ @Op_catd $B
        (@comp_cat_fapp0 $B (@Catd_cat $I) Cat_cat (@Sigma_func $I) $G) ];

// Whole projection view for canonical total base change on a section.
unif_rule @section_postcomp_sec $K _ _
    (@Op_funcd $K _ _ (@sigma_proj1_family_funcd $K $B $H))
    (@section_postcomp_sec $K _ _
      (@Op_funcd $K _ _
        (@comp_prod_fapp1_fapp0 Cat_cat _ _ _
          (Struct_sigma $H _) (Struct_sigma $H _)
          (Struct_sigma (@id (Functor_cat $K (@Catd_cat $B)) $H)
            (@sigma_pullback_total_transf $A $B $F)))) $s)
  ≡ @comp_fapp0 Cat_cat $K (Op_cat $A) (Op_cat $B) (@Op_func $A $B $F)
      (@section_postcomp_sec $K _ _
        (@Op_funcd $K _ _ (@sigma_proj1_family_funcd $K $A $H0)) $s)
  ↪ [ $H0 ≡ @comp_cat_fapp0 $K (@Catd_cat $B) (@Catd_cat $A)
        (@Pullback_catd_func $A $B $F) $H ];

// Canonical projection is preserved by the original fibrewise Sigma action.
unif_rule @section_postcomp_sec $K _ _
    (@Op_funcd $K _ _ (@sigma_proj1_family_funcd $K $A $D))
    (@section_postcomp_sec $K _ _
      (@Op_funcd $K _ _
        (@comp_prod_fapp1_fapp0 Cat_cat _ _ _
          (Struct_sigma $E (@Sigma_func $A)) (Struct_sigma $D (@Sigma_func $A))
          (Struct_sigma _ (@id (Functor_cat (@Catd_cat $A) Cat_cat) (@Sigma_func $A))))) $s)
  ≡ @section_postcomp_sec $K _ _
      (@Op_funcd $K _ _ (@sigma_proj1_family_funcd $K $A $E)) $s
  ↪ [ tt ≡ tt ];

// The canonical identity graph section has the identity inner base projection.
unif_rule @section_postcomp_sec (Op_cat $K) _ _
    (@Op_funcd (Op_cat $K) _ _
      (@sigma_proj1_family_funcd (Op_cat $K) $K (@hom_int $K $K (@id Cat_cat $K))))
    (@hom_identity_graph_sec $K)
  ≡ @id Cat_cat (Op_cat $K)
  ↪ [ tt ≡ tt ];

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
