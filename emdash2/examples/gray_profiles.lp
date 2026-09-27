/*
  Reviewer example: semantic strict-functor packages and the selected
  strict-object/lax-arrow Gray-hom profile.
*/

require open emdash.emdash3_2_represented_comma_families;

// Rigid ambient negative control, deliberately outside StrictFunctor.
injective symbol example_unprofiled_functor
  (A B : Cat)
  : τ (Functor A B);

// The generic strict-functor category is the sole classifier/rule owner.
assert [A B : Cat]
  (S : τ (@StrictFunctor A B)) ⊢
  S : τ (Obj (@StrictFunctor_cat A B));

assertnot [A B : Cat] ⊢
  @GrayHom_lax A B
  ≡ @StrictFunctor_cat A B;

assert [A B : Cat]
  (X Y : τ (Obj (@StrictFunctor_cat A B))) ⊢
  Hom_cat (@StrictFunctor_cat A B) X Y
  ≡ @Transf_cat
      A B
      (@strict_functor A B X)
      (@strict_functor A B Y);

assert [A B : Cat]
  (X : τ (Obj (@StrictFunctor_cat A B))) ⊢
  @fapp0
    (@StrictFunctor_cat A B)
    (@Functor_cat A B)
    (@strict_functor_include_func A B)
    X
  ≡ @strict_functor A B X;

assert [A B : Cat]
  (X Y : τ (Obj (@StrictFunctor_cat A B))) ⊢
  @fapp1_func
    (@StrictFunctor_cat A B)
    (@Functor_cat A B)
    (@strict_functor_include_func A B)
    X Y
  ≡ @id_func
      (@Transf_cat
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y));

assert [A B : Cat]
  (S : τ (@StrictFunctor A B)) ⊢
  S : τ (Obj (@GrayHom_lax A B));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B))) ⊢
  Hom_cat (@GrayHom_lax A B) X Y
  ≡ @LaxTransfor_cat
      A B
      (@strict_functor A B X)
      (@strict_functor A B Y);

assert [A B : Cat]
  (X : τ (Obj (@GrayHom_lax A B))) ⊢
  @fapp0
    (@GrayHom_lax A B)
    (@Functor_cat A B)
    (@grayhom_lax_include_func A B)
    X
  ≡ @strict_functor A B X;

// Identity and composition delegate to the shared ambient transfor tower.
assert [A B : Cat]
  (X : τ (Obj (@GrayHom_lax A B))) ⊢
  @id (@GrayHom_lax A B) X
  : τ (@LaxTransfor
      A B
      (@strict_functor A B X)
      (@strict_functor A B X));

assert [A B : Cat]
  (X Y Z : τ (Obj (@GrayHom_lax A B)))
  (g : τ (Hom (@GrayHom_lax A B) Y Z))
  (f : τ (Hom (@GrayHom_lax A B) X Y)) ⊢
  @comp_fapp0 (@GrayHom_lax A B) X Y Z g f
  : τ (@LaxTransfor
      A B
      (@strict_functor A B X)
      (@strict_functor A B Z));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B))) ⊢
  @fapp1_func
    (@GrayHom_lax A B)
    (@Functor_cat A B)
    (@grayhom_lax_include_func A B)
    X Y
  ≡ @lax_transfor_include_func
      A B
      (@strict_functor A B X)
      (@strict_functor A B Y);

// The next hom is the existing modification/higher-cell category.
assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B)))
  (eta theta : τ (Hom (@GrayHom_lax A B) X Y)) ⊢
  Hom_cat
    (Hom_cat (@GrayHom_lax A B) X Y)
    eta theta
  ≡ Hom_cat
      (@Transf_cat
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y))
      (@lax_transfor
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y)
        eta)
      (@lax_transfor
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y)
        theta);

assert [A : Cat] ⊢
  @strict_identity A
  : τ (Obj (@GrayHom_lax A A));

assert [A : Cat] ⊢
  @strict_identity_carrier_path A
  : τ (@=
      (Functor A A)
      (@strict_functor A A (@strict_identity A))
      (@id_func A));

// An ambient carrier plus strictness evidence enters the opaque classifier.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @make_strict_functor A B F p
  : τ (@StrictFunctor A B);

// Admission certificates are invisible at the opaque classifier boundary.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p q : τ (@IsStrictFunctor A B F)) ⊢
  @eq_refl
    (@StrictFunctor A B)
    (@make_strict_functor A B F p)
  : τ (@=
      (@StrictFunctor A B)
      (@make_strict_functor A B F p)
      (@make_strict_functor A B F q));

assertnot [A B : Cat]
  (F G : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  (q : τ (@IsStrictFunctor A B G)) ⊢
  @make_strict_functor A B F p
  ≡ @make_strict_functor A B G q;

// Carrier comparison is proof-time and is tested by typed reflexivity.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @eq_refl
    (Functor A B)
    (@strict_functor A B (@make_strict_functor A B F p))
  : τ (@=
      (Functor A B)
      (@strict_functor A B (@make_strict_functor A B F p))
      F);

// Classified strictness is reconstructed canonically, not projected from p.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor_is_strict
    A B (@make_strict_functor A B F p)
  : τ (@IsStrictFunctor
      A B
      (@strict_functor A B (@make_strict_functor A B F p)));

// Strictness is owned by the whole compositor transformation.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z)) ⊢
  p X Y Z g
  : τ (@IsStrictCell
      (@Functor_cat
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
      (@strict_functor_compositor_lhs_func A B F X Y Z g)
      (@strict_functor_compositor_rhs_func A B F X Y Z g)
      (@strict_functor_compositor_transf A B F X Y Z g));

// Capped evidence is a component projection of that whole property.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @strict_functor_compositor_evidence A B F p X Y Z g f
  : τ (@IsStrictCell
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@fapp1_compositor A B F X Y Z g f));

// The preferred stable-carrier comparison is proof-time and its transparent
// typed interface has a literal reflexivity body.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @make_strict_functor_carrier_path A B F p
  : τ (@=
      (Functor A B)
      (@strict_functor A B (@make_strict_functor A B F p))
      F);

// Constructor-visible point action computes through the ambient carrier.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  (X : τ (Obj A)) ⊢
  @fapp0 A B
    (@strict_functor A B (@make_strict_functor A B F p)) X
  ≡ @fapp0 A B F X;

// The explicit raw observation computes through whole and capped hom action.
assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  (X Y : τ (Obj A)) ⊢
  @fapp1_func A B
    (@strict_functor_underlying A B (@make_strict_functor A B F p))
    X Y
  ≡ @fapp1_func A B F X Y;

assert [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  [X Y : τ (Obj A)]
  (f : τ (Hom A X Y)) ⊢
  @fapp1_fapp0 A B
    (@strict_functor_underlying A B (@make_strict_functor A B F p))
    X Y f
  ≡ @fapp1_fapp0 A B F X Y f;

assertnot [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  [X Y : τ (Obj A)]
  (f : τ (Hom A X Y)) ⊢
  @fapp1_fapp0 A B
    (@strict_functor A B (@make_strict_functor A B F p)) X Y f
  ≡ @fapp1_fapp0 A B F X Y f;

// Composition is selected only by the stable evidence-bearing view.
assert [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B (@strict_functor A B S) X)
    (@fapp0 A B (@strict_functor A B S) Y)
    (@fapp0 A B (@strict_functor A B S) Z)
    (@fapp1_fapp0 A B (@strict_functor A B S) Y Z g)
    (@fapp1_fapp0 A B (@strict_functor A B S) X Y f)
  ≡ @fapp1_fapp0
      A B (@strict_functor A B S) X Z
      (@comp_fapp0 A X Y Z g f);

// The existing whole internal-action compositor itself computes to identity
// at the classified strict head; no second pointwise compositor is supplied.
assert [A B : Cat]
  (S : τ (@StrictFunctor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z)) ⊢
  @strict_functor_compositor_transf
    A B (@strict_functor A B S) X Y Z g
  ≡ @id
      (@Functor_cat
        (Hom_cat A X Y)
        (Hom_cat B
          (@fapp0 A B (@strict_functor A B S) X)
          (@fapp0 A B (@strict_functor A B S) Z)))
      (@strict_functor_compositor_lhs_func
        A B (@strict_functor A B S) X Y Z g);

// The two whole internal-hom accumulation views are guarded by the same
// strict package; capped computation above is their ordinary-arrow reading.
assert [A B : Cat]
  (S : τ (@StrictFunctor A B))
  (X Y Z : τ (Obj A))
  (g : τ (Hom A Y Z)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B
      (@fapp0 A B (@strict_functor A B S) X)
      (@fapp0 A B (@strict_functor A B S) Y))
    (Hom_cat B
      (@fapp0 A B (@strict_functor A B S) X)
      (@fapp0 A B (@strict_functor A B S) Z))
    (@hom_postcomp_func
      B A (@strict_functor A B S)
      (@fapp0 A B (@strict_functor A B S) X) Y Z g)
    (@fapp1_func A B (@strict_functor A B S) X Y)
  ≡ @comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat A X Z)
      (Hom_cat B
        (@fapp0 A B (@strict_functor A B S) X)
        (@fapp0 A B (@strict_functor A B S) Z))
      (@fapp1_func A B (@strict_functor A B S) X Z)
      (@hom_postcomp_func A A (@id_func A) X Y Z g);

assert [A B : Cat]
  (S : τ (@StrictFunctor A B))
  (W X Y : τ (Obj A))
  (h : τ (Hom A W X)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B
      (@fapp0 A B (@strict_functor A B S) X)
      (@fapp0 A B (@strict_functor A B S) Y))
    (Hom_cat B
      (@fapp0 A B (@strict_functor A B S) W)
      (@fapp0 A B (@strict_functor A B S) Y))
    (@hom_precomp_along_func
      A B (@strict_functor A B S)
      (@fapp0 A B (@strict_functor A B S) Y) W X h)
    (@fapp1_func A B (@strict_functor A B S) X Y)
  ≡ @comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat A W Y)
      (Hom_cat B
        (@fapp0 A B (@strict_functor A B S) W)
        (@fapp0 A B (@strict_functor A B S) Y))
      (@fapp1_func A B (@strict_functor A B S) W Y)
      (@hom_precomp_along_func A A (@id_func A) Y W X h);

// Strict ordinary transformations constrain the existing whole post/left
// laxity cell; no second naturality square or action hierarchy is introduced.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z)) ⊢
  (@strict_transfor_post_evidence A B F G epsilon p) X Y Z g
  : τ (@IsStrictCell
      (@Functor_cat
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z)))
      (@strict_transfor_naturality_lhs_func
        A B F G epsilon X Y Z g)
      (@strict_transfor_naturality_rhs_func
        A B F G epsilon X Y Z g)
      (@strict_transfor_naturality_transf
        A B F G epsilon X Y Z g));

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X)) ⊢
  (@strict_transfor_pre_evidence A B F G epsilon p) Y W X h
  : τ (@IsStrictCell
      (@Functor_cat
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
      (@strict_transfor_pre_naturality_lhs_func
        A B F G epsilon Y W X h)
      (@strict_transfor_pre_naturality_rhs_func
        A B F G epsilon Y W X h)
      (@strict_transfor_pre_naturality_transf
        A B F G epsilon Y W X h));

// The opaque full-strict classifier also has canonical semantic evidence.
assert [A B : Cat] [F G : τ (Functor A B)]
  (U : τ (@StrictTransfor A B F G)) ⊢
  @strict_transfor_is_strict A B F G U
  : τ (@IsStrictTransfor A B F G
      (@strict_transfor A B F G U));

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G)) ⊢
  @IsLaxTransfor A B F G epsilon
  ≡ @IsPreStrictTransfor A B F G epsilon;

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G)) ⊢
  @IsOplaxTransfor A B F G epsilon
  ≡ @IsPostStrictTransfor A B F G epsilon;

// A conventional lax transfor is admitted into an opaque classifier; the
// selected certificate is not projected afterward.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (lax : τ (@IsLaxTransfor A B F G epsilon)) ⊢
  @make_lax_transfor A B F G epsilon lax
  : τ (@LaxTransfor A B F G);

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (lax : τ (@IsLaxTransfor A B F G epsilon)) ⊢
  @lax_transfor_underlying A B F G
    (@make_lax_transfor A B F G epsilon lax)
  ≡ epsilon;

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (lax lax2 : τ (@IsLaxTransfor A B F G epsilon)) ⊢
  @eq_refl
    (@LaxTransfor A B F G)
    (@make_lax_transfor A B F G epsilon lax)
  : τ (@=
      (@LaxTransfor A B F G)
      (@make_lax_transfor A B F G epsilon lax)
      (@make_lax_transfor A B F G epsilon lax2));

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon theta : τ (Transf F G))
  (lax : τ (@IsLaxTransfor A B F G epsilon))
  (lax2 : τ (@IsLaxTransfor A B F G theta)) ⊢
  @make_lax_transfor A B F G epsilon lax
  ≡ @make_lax_transfor A B F G theta lax2;

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (lax : τ (@IsLaxTransfor A B F G epsilon)) ⊢
  @make_lax_transfor_carrier_path A B F G epsilon lax
  ≡ @eq_refl
      (Transf F G)
      (@lax_transfor A B F G
        (@make_lax_transfor A B F G epsilon lax));

// The opaque classifier has canonical semantic evidence independent of the
// hidden admission certificate.
assert [A B : Cat] [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G)) ⊢
  @lax_transfor_is_lax A B F G L
  : τ (@IsLaxTransfor A B F G (@lax_transfor A B F G L));

// Its exact existing pre/right whole cell computes to identity.
assert [A B : Cat] [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X)) ⊢
  @strict_transfor_pre_naturality_transf
    A B F G (@lax_transfor A B F G L) Y W X h
  ≡ @id
      (@Functor_cat
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
      (@strict_transfor_pre_naturality_lhs_func
        A B F G (@lax_transfor A B F G L) Y W X h);

// The stable lax view computes only the selected pre/right leg.
assert [A B : Cat] [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X))
  (f : τ (Hom A X Y)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F W)
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@tapp1_fapp0 A B F G X Y (@lax_transfor A B F G L) f)
    (@fapp1_fapp0 A B F W X h)
  ≡ @tapp1_fapp0
      A B F G W Y (@lax_transfor A B F G L)
      (@comp_fapp0 A W X Y f h);

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@fapp0 A B G Z)
    (@fapp1_fapp0 A B G Y Z g)
    (@tapp1_fapp0 A B F G X Y (@lax_transfor A B F G L) f)
  ≡ @tapp1_fapp0
      A B F G X Z (@lax_transfor A B F G L)
      (@comp_fapp0 A X Y Z g f);

assert [A B : Cat] [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (post : τ (@IsPostStrictTransfor A B F G epsilon))
  (pre : τ (@IsPreStrictTransfor A B F G epsilon)) ⊢
  @strict_transfor_strictness_intro A B F G epsilon post pre
  : τ (@IsStrictTransfor A B F G epsilon);

// Full strict transfors are admitted opaquely; evidence is not projected.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon)) ⊢
  @strict_transfor_underlying A B F G
    (@make_strict_transfor A B F G epsilon p)
  ≡ epsilon;

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p q : τ (@IsStrictTransfor A B F G epsilon)) ⊢
  @eq_refl
    (@StrictTransfor A B F G)
    (@make_strict_transfor A B F G epsilon p)
  : τ (@=
      (@StrictTransfor A B F G)
      (@make_strict_transfor A B F G epsilon p)
      (@make_strict_transfor A B F G epsilon q));

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon theta : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  (q : τ (@IsStrictTransfor A B F G theta)) ⊢
  @make_strict_transfor A B F G epsilon p
  ≡ @make_strict_transfor A B F G theta q;

// Capped evidence is evaluation of the whole strict cell.
assert [A B : Cat] [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (p : τ (@IsStrictTransfor A B F G epsilon))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @strict_transfor_naturality_evidence
    A B F G epsilon p X Y Z g f
  : τ (@IsStrictCell
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
      (@fapp0
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
        (@strict_transfor_naturality_lhs_func
          A B F G epsilon X Y Z g)
        f)
      (@fapp0
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
        (@strict_transfor_naturality_rhs_func
          A B F G epsilon X Y Z g)
        f)
      (@tapp1_post_laxity_cell A B F G epsilon X Y Z g f));

assert [A B : Cat] [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (p : τ (@IsStrictTransfor A B F G epsilon))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X))
  (q : τ (Hom A X Y)) ⊢
  @strict_transfor_pre_naturality_evidence
    A B F G epsilon p W X Y h q
  : τ (@IsStrictCell
      (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
      (@fapp0
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
        (@strict_transfor_pre_naturality_lhs_func
          A B F G epsilon Y W X h)
        q)
      (@fapp0
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
        (@strict_transfor_pre_naturality_rhs_func
          A B F G epsilon Y W X h)
        q)
      (@tapp1_pre_laxity_cell A B F G epsilon W X Y h q));

// The visible-admission carrier path is transparent reflexivity.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon)) ⊢
  @make_strict_transfor_carrier_path A B F G epsilon p
  ≡ @eq_refl
      (Transf F G)
      (@strict_transfor A B F G
        (@make_strict_transfor A B F G epsilon p));

// Raw observation computes through components and whole hom action.
assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  (X : τ (Obj A)) ⊢
  @tapp0_fapp0 A B F G X
    (@strict_transfor_underlying A B F G
      (@make_strict_transfor A B F G epsilon p))
  ≡ @tapp0_fapp0 A B F G X epsilon;

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  (X : τ (Obj A)) ⊢
  @tapp0_fapp0 A B F G X
    (@strict_transfor A B F G
      (@make_strict_transfor A B F G epsilon p))
  ≡ @tapp0_fapp0 A B F G X epsilon;

assert [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  (X Y : τ (Obj A)) ⊢
  @tapp1_func A B F G X Y
    (@strict_transfor_underlying A B F G
      (@make_strict_transfor A B F G epsilon p))
  ≡ @tapp1_func A B F G X Y epsilon;

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  (X Y : τ (Obj A)) ⊢
  @tapp1_func A B F G X Y
    (@strict_transfor A B F G
      (@make_strict_transfor A B F G epsilon p))
  ≡ @tapp1_func A B F G X Y epsilon;

// Post/left naturality computes only under the stable strict-transfor view.
assert [A B : Cat] [F G : τ (Functor A B)]
  (U : τ (@StrictTransfor A B F G))
  (X Y Z : τ (Obj A))
  (g : τ (Hom A Y Z)) ⊢
  @comp_cat_fapp0
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Y))
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
    (@hom_postcomp_func B A G (@fapp0 A B F X) Y Z g)
    (@tapp1_func A B F G X Y (@strict_transfor A B F G U))
  ≡ @comp_cat_fapp0
      (Hom_cat A X Y)
      (Hom_cat A X Z)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
      (@tapp1_func A B F G X Z (@strict_transfor A B F G U))
      (@hom_postcomp_func A A (@id_func A) X Y Z g);

assert [A B : Cat] [F G : τ (Functor A B)]
  (U : τ (@StrictTransfor A B F G))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@fapp0 A B G Z)
    (@fapp1_fapp0 A B G Y Z g)
    (@tapp1_fapp0
      A B F G X Y (@strict_transfor A B F G U) f)
  ≡ @tapp1_fapp0
      A B F G X Z (@strict_transfor A B F G U)
      (@comp_fapp0 A X Y Z g f);

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @comp_fapp0
    B
    (@fapp0 A B F X)
    (@fapp0 A B G Y)
    (@fapp0 A B G Z)
    (@fapp1_fapp0 A B G Y Z g)
    (@tapp1_fapp0 A B F G X Y epsilon f)
  ≡ @tapp1_fapp0 A B F G X Z epsilon
      (@comp_fapp0 A X Y Z g f);

assertnot [A B : Cat] [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  [X Y : τ (Obj A)]
  (g : τ (Hom A X Y)) ⊢
  @tapp1_fapp0 A B F G X Y epsilon g
  ≡ @hom_postcomp_fapp0
      B B (@id Cat_cat B)
      (@fapp0 A B F X)
      (@fapp0 A B G X)
      (@fapp0 A B G Y)
      (@fapp1_fapp0 A B G X Y g)
      (@tapp0_fapp0 A B F G X epsilon);

// A strict displayed functor constrains the existing laxity transformation.
assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y)) ⊢
  p x y f
  : τ (@IsStrictCell
      (@Functor_cat (Fibre_cat E x) (Fibre_cat D y))
      (@functord_transport_lhs_func K E D FF x y f)
      (@functord_transport_rhs_func K E D FF x y f)
      (@functord_laxity_transf K E D FF x y f));

assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF)) ⊢
  @strict_functord_underlying K E D
    (@make_strict_functord K E D FF p)
  ≡ FF;

assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p q : τ (@IsStrictFunctord K E D FF)) ⊢
  @eq_refl
    (@StrictFunctord K E D)
    (@make_strict_functord K E D FF p)
  : τ (@=
      (@StrictFunctord K E D)
      (@make_strict_functord K E D FF p)
      (@make_strict_functord K E D FF q));

assertnot [K : Cat] [E D : τ (Catd K)]
  (FF GG : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF))
  (q : τ (@IsStrictFunctord K E D GG)) ⊢
  @make_strict_functord K E D FF p
  ≡ @make_strict_functord K E D GG q;

assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat E D x
    (@strict_functord_underlying K E D
      (@make_strict_functord K E D FF p))
  ≡ @tapp0_fapp0 K Cat_cat E D x FF;

assertnot [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF))
  (x : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat E D x
    (@strict_functord K E D
      (@make_strict_functord K E D FF p))
  ≡ @tapp0_fapp0 K Cat_cat E D x FF;

assert [K : Cat] [E D : τ (Catd K)]
  [FF : τ (Functord E D)]
  (p : τ (@IsStrictFunctord K E D FF))
  [x y : τ (Obj K)]
  (f : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x))) ⊢
  @strict_functord_laxity_evidence K E D FF p x y f u
  : τ (@IsStrictCell
      (Fibre_cat D y)
      (@fapp0
        (Fibre_cat E x) (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y f) u)
      (@fapp0
        (Fibre_cat E x) (Fibre_cat D y)
        (@functord_transport_rhs_func K E D FF x y f) u)
      (@tapp0_fapp0
        (Fibre_cat E x) (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y f)
        (@functord_transport_rhs_func K E D FF x y f)
        u
        (@functord_laxity_transf K E D FF x y f)));

// The target/right reading is available only through the strict profile.
assert [K : Cat] [E D : τ (Catd K)]
  (S : τ (@StrictFunctord K E D))
  (x y : τ (Obj K)) ⊢
  @strict_functord_transport_rhs_tele_path K E D S x y
  : τ (@=
      (Functor
        (Hom_cat K x y)
        (Functor_cat (Fibre_cat E x) (Fibre_cat D y)))
      (@tapp1_func K Cat_cat E D x y (@strict_functord K E D S))
      (@functord_transport_rhs_tele_func
        K E D (@strict_functord K E D S) x y));

assert [K : Cat] [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (strict : τ (@IsStrictFunctord K E D FF))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y)) ⊢
  @strict_cell_path
    (@Functor_cat (Fibre_cat E x) (Fibre_cat D y))
    (@functord_transport_lhs_func K E D FF x y p)
    (@functord_transport_rhs_func K E D FF x y p)
    (@functord_laxity_transf K E D FF x y p)
    (strict x y p)
  : τ (@=
      (Functor (Fibre_cat E x) (Fibre_cat D y))
      (@functord_transport_lhs_func K E D FF x y p)
      (@functord_transport_rhs_func K E D FF x y p));

// Every opaque classified object owns canonical evidence about the one
// intrinsic compositor; the admission certificate is not recoverable.
assert [A B : Cat]
  (S : τ (@StrictFunctor A B)) ⊢
  @strict_functor_is_strict A B S
  : τ (@IsStrictFunctor
      A B (@strict_functor A B S));

// An ambient compositor is typed between its two retained endpoints; those
// endpoints are no longer convertible, so a literal identity comparison is
// not even the appropriate judgment.
assert [A B : Cat]
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor
    A B (@example_unprofiled_functor A B) X Y Z g f
  : τ (Hom
      (Hom_cat
        B
        (@fapp0 A B (@example_unprofiled_functor A B) X)
        (@fapp0 A B (@example_unprofiled_functor A B) Z))
      (@strict_functor_compositor_lhs
        A B (@example_unprofiled_functor A B) X Y Z g f)
      (@strict_functor_compositor_rhs
        A B (@example_unprofiled_functor A B) X Y Z g f));

assertnot [A B : Cat]
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @strict_functor_compositor_lhs
    A B (@example_unprofiled_functor A B) X Y Z g f
  ≡ @strict_functor_compositor_rhs
      A B (@example_unprofiled_functor A B) X Y Z g f;

// The evidence-bearing whole view is deliberately retained; it is not a
// runtime alias of the raw carrier.
assertnot [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor A B (@make_strict_functor A B F p)
  ≡ F;
