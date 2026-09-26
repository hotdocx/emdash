/*
  Reviewer example: semantic strict-functor packages and the selected
  strict-object/lax-arrow Gray-hom profile.
*/

require open emdash.emdash3_2_gray_profiles;

// Rigid ambient negative control, deliberately outside StrictFunctor.
injective symbol example_unprofiled_functor
  (A B : Cat)
  : τ (Functor A B);

assert [A B : Cat]
  (S : τ (@StrictFunctor A B)) ⊢
  S : τ (Obj (@GrayHom_lax A B));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B))) ⊢
  Hom_cat (@GrayHom_lax A B) X Y
  ≡ @Transf_cat
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
  : τ (Hom
      (@Functor_cat A B)
      (@strict_functor A B X)
      (@strict_functor A B X));

assert [A B : Cat]
  (X Y Z : τ (Obj (@GrayHom_lax A B)))
  (g : τ (Hom (@GrayHom_lax A B) Y Z))
  (f : τ (Hom (@GrayHom_lax A B) X Y)) ⊢
  @comp_fapp0 (@GrayHom_lax A B) X Y Z g f
  : τ (Hom
      (@Functor_cat A B)
      (@strict_functor A B X)
      (@strict_functor A B Z));

assert [A B : Cat]
  (X Y : τ (Obj (@GrayHom_lax A B))) ⊢
  @fapp1_func
    (@GrayHom_lax A B)
    (@Functor_cat A B)
    (@grayhom_lax_include_func A B)
    X Y
  ≡ @id_func
      (@Transf_cat
        A B
        (@strict_functor A B X)
        (@strict_functor A B Y));

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
      eta theta;

assert [A : Cat] ⊢
  @strict_identity A
  : τ (Obj (@GrayHom_lax A A));

assert [A : Cat] ⊢
  @strict_identity_carrier_path A
  : τ (@=
      (Functor A A)
      (@strict_functor A A (@strict_identity A))
      (@id_func A));

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

// Arbitrary nonidentity arrows and their next Hom action use the shared
// ambient transformation tower under both whole and capped observations.
assert [A B : Cat] (S T : τ (@StrictFunctor A B))
  (epsilon : τ (@Transf A B (@strict_functor A B S) (@strict_functor A B T))) ⊢
  @fapp1_fapp0 (@StrictFunctor_cat A B) (@Functor_cat A B)
    (@strict_functor_include_func A B) S T epsilon
  ≡ epsilon;

assert [A B : Cat] (S T : τ (@StrictFunctor A B))
  (epsilon theta : τ (@Transf A B (@strict_functor A B S) (@strict_functor A B T)))
  (alpha : τ (Hom (@Transf_cat A B (@strict_functor A B S) (@strict_functor A B T)) epsilon theta)) ⊢
  @fapp1_fapp0
    (@Transf_cat A B (@strict_functor A B S) (@strict_functor A B T))
    (@Transf_cat A B (@strict_functor A B S) (@strict_functor A B T))
    (@fapp1_func (@StrictFunctor_cat A B) (@Functor_cat A B)
      (@strict_functor_include_func A B) S T)
    epsilon theta alpha
  ≡ alpha;

// Observe identity and composition through the whole inclusion. This checks
// both orders: category cuts first, or the inclusion's Hom projection first.
assert [A B : Cat] (S : τ (@StrictFunctor A B)) ⊢
  @fapp1_fapp0 (@StrictFunctor_cat A B) (@Functor_cat A B)
    (@strict_functor_include_func A B) S S
    (@id (@StrictFunctor_cat A B) S)
  ≡ @id (@Functor_cat A B) (@strict_functor A B S);

assert [A B : Cat] (S T U : τ (@StrictFunctor A B))
  (g : τ (@Transf A B (@strict_functor A B T) (@strict_functor A B U)))
  (f : τ (@Transf A B (@strict_functor A B S) (@strict_functor A B T))) ⊢
  @fapp1_fapp0 (@StrictFunctor_cat A B) (@Functor_cat A B)
    (@strict_functor_include_func A B) S U
    (@comp_fapp0 (@StrictFunctor_cat A B) S T U g f)
  ≡ @comp_fapp0 (@Functor_cat A B)
      (@strict_functor A B S) (@strict_functor A B T)
      (@strict_functor A B U) g f;

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

// Composition computes at the stable evidence-bearing view.
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

// The retired code-specific literal-id computation does not leak to a rigid
// ambient functor.
assertnot [A B : Cat]
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y)) ⊢
  @fapp1_compositor
    A B (@example_unprofiled_functor A B) X Y Z g f
  ≡ @id
      (Hom_cat
        B
        (@fapp0 A B (@example_unprofiled_functor A B) X)
        (@fapp0 A B (@example_unprofiled_functor A B) Z))
      (@strict_functor_compositor_lhs
        A B (@example_unprofiled_functor A B) X Y Z g f);

// Opaque package raw/stable observations compare only at proof time.
assert [A B : Cat] (S : τ (@StrictFunctor A B)) ⊢
  @eq_refl (Functor A B) (@strict_functor_underlying A B S)
  : τ (@= (Functor A B) (@strict_functor_underlying A B S) (@strict_functor A B S));

assertnot [A B : Cat] (F G : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) (q : τ (@IsStrictFunctor A B G)) ⊢
  @eq_refl (@StrictFunctor A B) (@make_strict_functor A B F p)
  : τ (@= (@StrictFunctor A B) (@make_strict_functor A B F p) (@make_strict_functor A B G q));

// The stable carrier is not a runtime decoder of an admission.
assertnot [A B : Cat] (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F)) ⊢
  @strict_functor A B (@make_strict_functor A B F p) ≡ F;
