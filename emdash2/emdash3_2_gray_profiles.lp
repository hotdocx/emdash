/*
  Emdash v3.2: strict-functor classifier and one Gray-hom profile.

  IsStrictFunctor constrains the existing extracted compositor by an endpoint
  path and equality to the corresponding path_to_hom. StrictFunctor is the
  opaque full-image classifier admitted from an ambient carrier and that
  property. Its stable strict_functor view retains the profile discriminator:
  point action exposes a visible admitted carrier, while hom action compares
  propositionally.

  StrictFunctor_cat is the full subcategory on those opaque objects and
  owns the whole inclusion into Functor_cat. GrayHom_lax has the same strict
  objects but restricts its homs to exact LaxTransfor packages; their higher
  homs reuse ambient modifications and every subsequent iterated cell. The same file
  also classifies the two skew ordinary-transformation profiles by constraining
  the existing post/left or pre/right whole cell. `IsStrictTransfor` carries
  both evidence families; `IsLaxTransfor` selects the pre-strict leg while
  retaining the post cell. Its stable `lax_transfor` view owns exactly that
  one-sided computation. No parallel `tapp1` hierarchy is introduced. The
  displayed `IsStrictFunctord` property likewise constrains the existing
  whole-in-fibre-object laxity transformation and adds no `fdapp1s` hierarchy.
  The I tensor I consumer confirms that selected lax direction.
*/

require open emdash.emdash3_2;

// Whole post/left source of the intrinsic functor compositor.
symbol strict_functor_compositor_lhs_func
  [A B : Cat]
  (F : τ (Functor A B))
  (X : τ (Obj A))
  [Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  : τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
≔ @functord_transport_lhs_func
    A
    (@hom_ A A (@id_func A) X)
    (@hom_ B A F (@fapp0 A B F X))
    (@fapp1_at_transf A B F X)
    Y Z g;

// Whole post/left target of the intrinsic functor compositor.
symbol strict_functor_compositor_rhs_func
  [A B : Cat]
  (F : τ (Functor A B))
  (X : τ (Obj A))
  [Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  : τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
≔ @functord_transport_rhs_func
    A
    (@hom_ A A (@id_func A) X)
    (@hom_ B A F (@fapp0 A B F X))
    (@fapp1_at_transf A B F X)
    Y Z g;

// Formal post/left endpoint of the extracted ordinary compositor.
symbol strict_functor_compositor_lhs
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom B (fapp0 F X) (fapp0 F Z))
≔ @fapp0
    (Hom_cat A X Y)
    (Hom_cat B (fapp0 F X) (fapp0 F Z))
    (@strict_functor_compositor_lhs_func A B F X Y Z g)
    f;

// Formal pre/right endpoint of the extracted ordinary compositor.
symbol strict_functor_compositor_rhs
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom B (fapp0 F X) (fapp0 F Z))
≔ @fapp0
    (Hom_cat A X Y)
    (Hom_cat B (fapp0 F X) (fapp0 F Z))
    (@strict_functor_compositor_rhs_func A B F X Y Z g)
    f;

/*
  Semantic strictness of one existing cell. The endpoint path is explicit, so
  the property remains meaningful after the global strict endpoint cuts are
  migrated. The second field constrains the existing cell; it does not supply
  another compositor.
*/
symbol IsStrictCell
  [C : Cat]
  [x y : τ (Obj C)]
  (cell : τ (Hom C x y))
  : Grpd
≔ `Σ_ p : τ (@= (Obj C) x y),
    @= (Hom C x y) cell (@path_to_hom C x y p);

symbol strict_cell_path
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (e : τ (@IsStrictCell C x y cell))
  : τ (@= (Obj C) x y)
≔ sigma_Fst e;

symbol strict_cell_agreement
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (e : τ (@IsStrictCell C x y cell))
  : τ (@= (Hom C x y)
      cell
      (@path_to_hom C x y (@strict_cell_path C x y cell e)))
≔ sigma_Snd e;

// Whole intrinsic compositor transformation before capping at f:X->Y.
symbol strict_functor_compositor_transf
  [A B : Cat]
  (F : τ (Functor A B))
  (X : τ (Obj A))
  [Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  : τ (Transf
      (@strict_functor_compositor_lhs_func A B F X Y Z g)
      (@strict_functor_compositor_rhs_func A B F X Y Z g))
≔ @tapp1_post_laxity_transf
    A B F F (@id (Functor_cat A B) F) X Y Z g;

// Normal strict-functor property over the whole intrinsic compositor. Capped
// evidence is derived below by component evaluation.
symbol IsStrictFunctor
  [A B : Cat]
  (F : τ (Functor A B))
  : Grpd
≔ @Pi_grpd
    (Obj A)
    (λ X : τ (Obj A),
      @Pi_grpd
        (Obj A)
        (λ Y : τ (Obj A),
          @Pi_grpd
            (Obj A)
            (λ Z : τ (Obj A),
              @Pi_grpd
                (Hom A Y Z)
                (λ g : τ (Hom A Y Z),
                  @IsStrictCell
                    (@Functor_cat
                      (Hom_cat A X Y)
                      (Hom_cat B
                        (@fapp0 A B F X)
                        (@fapp0 A B F Z)))
                    (@strict_functor_compositor_lhs_func
                      A B F X Y Z g)
                    (@strict_functor_compositor_rhs_func
                      A B F X Y Z g)
                    (@strict_functor_compositor_transf
                      A B F X Y Z g)))));

// Evaluating an equality-induced whole transformation agrees with the
// equality-induced arrow of the evaluated endpoint path.
symbol tapp0_path_to_hom
  [K D : Cat]
  [F G : τ (Functor K D)]
  (p : τ (@= (Functor K D) F G))
  (x : τ (Obj K))
  : τ (@=
      (Hom D (@fapp0 K D F x) (@fapp0 K D G x))
      (@tapp0_fapp0
        K D F G x
        (@path_to_hom (Functor_cat K D) F G p))
      (@path_to_hom
        D
        (@fapp0 K D F x)
        (@fapp0 K D G x)
        (@eq_ap
          (Functor K D)
          (Obj D)
          (λ H : τ (Functor K D), @fapp0 K D H x)
          F G p)))
≔ @ind_eqr
    (Functor K D)
    G
    (λ H : τ (Functor K D),
      λ q : τ (@= (Functor K D) H G),
        @=
          (Hom D (@fapp0 K D H x) (@fapp0 K D G x))
          (@tapp0_fapp0
            K D H G x
            (@path_to_hom (Functor_cat K D) H G q))
          (@path_to_hom
            D
            (@fapp0 K D H x)
            (@fapp0 K D G x)
            (@eq_ap
              (Functor K D)
              (Obj D)
              (λ J : τ (Functor K D), @fapp0 K D J x)
              H G q)))
    (@eq_refl
      (Hom D (@fapp0 K D G x) (@fapp0 K D G x))
      (@id D (@fapp0 K D G x)))
    F p;

// Endpoint path of the capped compositor, obtained by evaluating the whole
// strictness endpoint path at f.
symbol strict_functor_compositor_component_path
  [A B : Cat]
  [F : τ (Functor A B)]
  (strict : τ (@IsStrictFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@strict_functor_compositor_rhs A B F X Y Z g f))
≔ @eq_ap
    (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
    (Obj (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
    (λ H : τ (Functor
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))),
      @fapp0
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
        H f)
    (@strict_functor_compositor_lhs_func A B F X Y Z g)
    (@strict_functor_compositor_rhs_func A B F X Y Z g)
    (@strict_cell_path
      (@Functor_cat
        (Hom_cat A X Y)
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
      (@strict_functor_compositor_lhs_func A B F X Y Z g)
      (@strict_functor_compositor_rhs_func A B F X Y Z g)
      (@strict_functor_compositor_transf A B F X Y Z g)
      (strict X Y Z g));

// Capped compositor agreement, derived by evaluating the whole cell equality
// and then using tapp0_path_to_hom for its equality-induced target.
symbol strict_functor_compositor_component_agreement
  [A B : Cat]
  [F : τ (Functor A B)]
  (strict : τ (@IsStrictFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
        (@strict_functor_compositor_lhs A B F X Y Z g f)
        (@strict_functor_compositor_rhs A B F X Y Z g f))
      (@fapp1_compositor A B F X Y Z g f)
      (@path_to_hom
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
        (@strict_functor_compositor_lhs A B F X Y Z g f)
        (@strict_functor_compositor_rhs A B F X Y Z g f)
        (@strict_functor_compositor_component_path
          A B F strict X Y Z g f)))
≔ @eq_trans
    (Hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@strict_functor_compositor_rhs A B F X Y Z g f))
    (@fapp1_compositor A B F X Y Z g f)
    (@tapp0_fapp0
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs_func A B F X Y Z g)
      (@strict_functor_compositor_rhs_func A B F X Y Z g)
      f
      (@path_to_hom
        (@Functor_cat
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
        (@strict_functor_compositor_lhs_func A B F X Y Z g)
        (@strict_functor_compositor_rhs_func A B F X Y Z g)
        (@strict_cell_path
          (@Functor_cat
            (Hom_cat A X Y)
            (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
          (@strict_functor_compositor_lhs_func A B F X Y Z g)
          (@strict_functor_compositor_rhs_func A B F X Y Z g)
          (@strict_functor_compositor_transf A B F X Y Z g)
          (strict X Y Z g))))
    (@path_to_hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@strict_functor_compositor_component_path
        A B F strict X Y Z g f))
    (@eq_ap
      (Hom
        (@Functor_cat
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
        (@strict_functor_compositor_lhs_func A B F X Y Z g)
        (@strict_functor_compositor_rhs_func A B F X Y Z g))
      (Hom
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
        (@strict_functor_compositor_lhs A B F X Y Z g f)
        (@strict_functor_compositor_rhs A B F X Y Z g f))
      (λ theta : τ (Hom
          (@Functor_cat
            (Hom_cat A X Y)
            (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
          (@strict_functor_compositor_lhs_func A B F X Y Z g)
          (@strict_functor_compositor_rhs_func A B F X Y Z g)),
        @tapp0_fapp0
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
          (@strict_functor_compositor_lhs_func A B F X Y Z g)
          (@strict_functor_compositor_rhs_func A B F X Y Z g)
          f theta)
      (@strict_functor_compositor_transf A B F X Y Z g)
      (@path_to_hom
        (@Functor_cat
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
        (@strict_functor_compositor_lhs_func A B F X Y Z g)
        (@strict_functor_compositor_rhs_func A B F X Y Z g)
        (@strict_cell_path
          (@Functor_cat
            (Hom_cat A X Y)
            (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
          (@strict_functor_compositor_lhs_func A B F X Y Z g)
          (@strict_functor_compositor_rhs_func A B F X Y Z g)
          (@strict_functor_compositor_transf A B F X Y Z g)
          (strict X Y Z g)))
      (@strict_cell_agreement
        (@Functor_cat
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
        (@strict_functor_compositor_lhs_func A B F X Y Z g)
        (@strict_functor_compositor_rhs_func A B F X Y Z g)
        (@strict_functor_compositor_transf A B F X Y Z g)
        (strict X Y Z g)))
    (@tapp0_path_to_hom
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs_func A B F X Y Z g)
      (@strict_functor_compositor_rhs_func A B F X Y Z g)
      (@strict_cell_path
        (@Functor_cat
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
        (@strict_functor_compositor_lhs_func A B F X Y Z g)
        (@strict_functor_compositor_rhs_func A B F X Y Z g)
        (@strict_functor_compositor_transf A B F X Y Z g)
        (strict X Y Z g))
      f);

// Public capped strictness evidence projected from the whole property.
symbol strict_functor_compositor_evidence
  [A B : Cat]
  [F : τ (Functor A B)]
  (strict : τ (@IsStrictFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@IsStrictCell
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@fapp1_compositor A B F X Y Z g f))
≔ Struct_sigma
    (@strict_functor_compositor_component_path
      A B F strict X Y Z g f)
    (@strict_functor_compositor_component_agreement
      A B F strict X Y Z g f);

// Opaque full-image classifier of ambient carriers admitting strictness.
injective symbol StrictFunctor
  (A B : Cat)
  : Grpd;

/*
  Admission constructor. The supplied property is an admission certificate;
  it is internalized and has no projection from the resulting opaque object.
  This symbol is deliberately not injective: its custom proof-time comparison
  below ignores certificate choice while retaining the carrier obligation.
*/
symbol make_strict_functor
  [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  : τ (@StrictFunctor A B);

// Stable ambient view; strict computation matches this retained head.
injective symbol strict_functor
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  : τ (Functor A B);

/*
  Explicit raw-carrier observation. Unlike the stable strict_functor view,
  this owner intentionally computes on a visible admission constructor and is
  used only when a consumer asks to leave the strict profile.
*/
injective symbol strict_functor_underlying
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  : τ (Functor A B);

rule @strict_functor_underlying _ _
      (@make_strict_functor _ _ $F _)
  ↪ $F;

// The raw and stable observations compare proof-time for an arbitrary opaque
// strict object; runtime strict action continues to match strict_functor.
unif_rule
  @strict_functor_underlying $A $B $S
  ≡ @strict_functor $A $B $S
  ↪ [ tt ≡ tt ];

/*
  Proof-time visible-admission carrier comparison.

  The strict realization remains a stable runtime head. During elaboration,
  a visible admission compares with its raw carrier; the named path below makes
  the same comparison explicit when a consumer needs a proof term.

  This is intentionally a unification rule rather than

    strict_functor(make_strict_functor(F,p)) --> F,

  which would erase the discriminator needed by later profile-local strict
  computation.
*/
unif_rule
  @strict_functor $A $B
    (@make_strict_functor $A $B $F _)
  ≡ $F
  ↪ [ tt ≡ tt ];

/*
  Full-image certificate insensitivity. Two admitted objects compare exactly
  when their rigid ambient carriers compare; no witness projection survives.
*/
unif_rule
  @make_strict_functor $A $B $F _
  ≡ @make_strict_functor $A $B $G _
  ↪ [ $F ≡ $G ];

// Typed interface to the proof-time carrier comparison. Its transparent body
// is literally reflexivity; computational consumers use the raw-carrier
// observation above rather than trying to suspend this proof under J.
symbol make_strict_functor_carrier_path
  [A B : Cat]
  (F : τ (Functor A B))
  (p : τ (@IsStrictFunctor A B F))
  : τ (@=
      (Functor A B)
      (@strict_functor A B (@make_strict_functor A B F p))
      F)
≔ @eq_refl
    (Functor A B)
    (@strict_functor A B (@make_strict_functor A B F p));

// Constructor-visible point action exposes the admitted carrier while whole
// hom action stays under the strict_functor head.
// lhs-audit: keep 3 -- make_strict_functor is the semantic admission
// discriminator and preserves the classified whole view otherwise.
rule @fapp0 _ _
      (@strict_functor $A $B (@make_strict_functor $A $B $F _)) $x
  ↪ @fapp0 $A $B $F $x;

// Profile-local capped strict composition. The classified functor head
// remains visible; this rule intentionally overlaps the temporary ambient cut
// with the identical RHS until that global rule is removed.
rule @comp_fapp0
      $B _ _ _
      (@fapp1_fapp0
        $A $B (@strict_functor $A $B $S) $Y $Z $g)
      (@fapp1_fapp0
        $A $B (@strict_functor $A $B $S) $X $Y $f)
  ↪ @fapp1_fapp0
      $A $B (@strict_functor $A $B $S) $X $Z
      (@comp_fapp0 $A $X $Y $Z $g $f);

// Whole post/left strict functoriality for the classified stable view.
rule @comp_fapp0
      Cat_cat _ _ _
      (@hom_postcomp_func
        $B $A (@strict_functor $A $B $S) _ $Y $Z $g)
      (@fapp1_func
        $A $B (@strict_functor $A $B $S) $X $Y)
  ↪ @comp_fapp0
      Cat_cat _ _ _
      (@fapp1_func
        $A $B (@strict_functor $A $B $S) $X $Z)
      (@hom_postcomp_func $A $A (@id_func $A) $X $Y $Z $g);

// Whole pre/right strict functoriality for the same profile.
rule @comp_fapp0
      Cat_cat _ _ _
      (@hom_precomp_along_func
        $A $B (@strict_functor $A $B $S)
        (@fapp0 $A $B (@strict_functor $A $B $S) $Y)
        $W $X $h)
      (@fapp1_func
        $A $B (@strict_functor $A $B $S) $X $Y)
  ↪ @comp_fapp0
      Cat_cat _ _ _
      (@fapp1_func
        $A $B (@strict_functor $A $B $S) $W $Y)
      (@hom_precomp_along_func $A $A (@id_func $A) $Y $W $X $h);

// Profile-owned represented postcomposition accumulation (API-04P).
// The outer ambient category remains tied to the strict view.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_postcomp_func $A $B (@strict_functor $B $A $S) $W $Y $Z $q)
      (@hom_postcomp_func $A $B (@strict_functor $B $A $S) $W $X $Y $p)
  ↪ @hom_postcomp_func
      $A $B (@strict_functor $B $A $S) $W $X $Z
      (@comp_fapp0 $B $X $Y $Z $q $p);

rule @hom_postcomp_fapp0
      $A $B (@strict_functor $B $A $S) $W $Y $Z $q
      (@hom_postcomp_fapp0 $A $B (@strict_functor $B $A $S) $W $X $Y $p $g)
  ↪ @hom_postcomp_fapp0
      $A $B (@strict_functor $B $A $S) $W $X $Z
      (@comp_fapp0 $B $X $Y $Z $q $p)
      $g;

rule @comp_fapp0
      $A
      _
      _
      _
      (@fapp1_fapp0 $B $A (@strict_functor $B $A $S) $Y $Z $q)
      (@hom_postcomp_fapp0 $A $B (@strict_functor $B $A $S) $W $X $Y $p $g)
  ↪ @hom_postcomp_fapp0
      $A
      $B
      (@strict_functor $B $A $S)
      $W
      $X
      $Z
      (@comp_fapp0 $B $X $Y $Z $q $p)
      $g;

// Profile-owned represented precomposition accumulation.
// Functor-level contravariant accumulation of consecutive precomposition actions.
rule @comp_fapp0
      Cat_cat
      _ _ _
      (@hom_precomp_along_func $A $B (@strict_functor $A $B $S) $Z $W $X $p)
      (@hom_precomp_along_func $A $B (@strict_functor $A $B $S) $Z $X $Y $q)
  ↪ @hom_precomp_along_func
      $A $B (@strict_functor $A $B $S) $Z $W $Y
      (@comp_fapp0 $A $W $X $Y $q $p);

// Point-level contravariant accumulation of consecutive precomposition actions.
rule @hom_precomp_along_fapp0
      $A $B (@strict_functor $A $B $S) $Z $W $X $p
      (@hom_precomp_along_fapp0 $A $B (@strict_functor $A $B $S) $Z $X $Y $q $g)
  ↪ @hom_precomp_along_fapp0
      $A $B (@strict_functor $A $B $S) $Z $W $Y
      (@comp_fapp0 $A $W $X $Y $q $p)
      $g;

// Raw adjacent-source precomposition fold:
// ((F[p])^*(g)) o F[q] -> (F[p o q])^*(g).
rule @comp_fapp0
      $B
      _
      _
      _
      (@hom_precomp_along_fapp0 $A $B (@strict_functor $A $B $S) $Z $W $X $p $g)
      (@fapp1_fapp0 $A $B (@strict_functor $A $B $S) $V $W $q)
  ↪ @hom_precomp_along_fapp0
      $A
      $B
      (@strict_functor $A $B $S)
      $Z
      $V
      $X
      (@comp_fapp0 $A $V $W $X $p $q)
      $g;

/*
  Whole intrinsic compositor computation for a classified strict carrier.

  This is the existing internal-action cell at its final stable projection
  owner. The source/target family slots are inferred; the repeated
  fapp1_at_transf/fdapp1_int_transfd action is the semantic discriminator.
  No second compositor or pointwise strictness field is introduced.
*/
rule @fdapp1_comma_projection_transf
      $A _ _
      (@fapp1_at_transf
        $A $B (@strict_functor $A $B $S) $X)
      (@fdapp1_int_transfd
        $A _ _
        (@fapp1_at_transf
          $A $B (@strict_functor $A $B $S) $X))
      $Y $Z $g
  ↪ @id
      (@Functor_cat
        (Hom_cat $A $X $Y)
        (Hom_cat
          $B
          (@fapp0 $A $B (@strict_functor $A $B $S) $X)
          (@fapp0 $A $B (@strict_functor $A $B $S) $Z)))
      (@strict_functor_compositor_lhs_func
        $A $B (@strict_functor $A $B $S) $X $Y $Z $g);

/*
  Canonical strictness of every classified object. Both fields compute by
  reflexivity from the profile-local endpoint and whole-compositor rules; no
  admission certificate is recovered or stored.
*/
symbol strict_functor_is_strict
  [A B : Cat]
  (S : τ (@StrictFunctor A B))
  : τ (@IsStrictFunctor A B (@strict_functor A B S))
≔ λ X : τ (Obj A),
  λ Y : τ (Obj A),
  λ Z : τ (Obj A),
  λ g : τ (Hom A Y Z),
    Struct_sigma
      (@eq_refl
        (Functor
          (Hom_cat A X Y)
          (Hom_cat B
            (@fapp0 A B (@strict_functor A B S) X)
            (@fapp0 A B (@strict_functor A B S) Z)))
        (@strict_functor_compositor_lhs_func
          A B (@strict_functor A B S) X Y Z g))
      (@eq_refl
        (Hom
          (@Functor_cat
            (Hom_cat A X Y)
            (Hom_cat B
              (@fapp0 A B (@strict_functor A B S) X)
              (@fapp0 A B (@strict_functor A B S) Z)))
          (@strict_functor_compositor_lhs_func
            A B (@strict_functor A B S) X Y Z g)
          (@strict_functor_compositor_rhs_func
            A B (@strict_functor A B S) X Y Z g))
        (@strict_functor_compositor_transf
          A B (@strict_functor A B S) X Y Z g));

// Supplied identity strictness proof; its internal derivation remains later.
constant symbol identity_is_strict
  (A : Cat)
  : τ (@IsStrictFunctor A A (@id_func A));

symbol strict_identity
  (A : Cat)
  : τ (@StrictFunctor A A)
≔ @make_strict_functor A A (@id_func A) (@identity_is_strict A);

// Whole semantic observation of the classified identity view, derived
// transparently from the generic visible-admission carrier comparison.
symbol strict_identity_carrier_path
  (A : Cat)
  : τ (@=
      (Functor A A)
      (@strict_functor A A (@strict_identity A))
      (@id_func A))
≔ @make_strict_functor_carrier_path
    A A (@id_func A) (@identity_is_strict A);

// Sheaf-style full subcategory on strict-functor objects. Its arrows remain
// the ambient lax/coherent transfors and every higher hom is reused.
injective symbol StrictFunctor_cat
  (A B : Cat)
  : Cat;

rule Obj (@StrictFunctor_cat $A $B)
  ↪ @StrictFunctor $A $B;

rule Hom_cat (@StrictFunctor_cat $A $B) $X $Y
  ↪ @Transf_cat
      $A $B
      (@strict_functor $A $B $X)
      (@strict_functor $A $B $Y);

// Identity delegates to the ambient functor category.
rule @id (@StrictFunctor_cat $A $B) $X
  ↪ @id
      (@Functor_cat $A $B)
      (@strict_functor $A $B $X);

// Composition delegates to the ambient functor category.
// lhs-audit: keep 2,3,4 -- the carrier projections occur on the RHS.
rule @comp_fapp0
      (@StrictFunctor_cat $A $B) $X $Y $Z $g $f
  ↪ @comp_fapp0
      (@Functor_cat $A $B)
      (@strict_functor $A $B $X)
      (@strict_functor $A $B $Y)
      (@strict_functor $A $B $Z)
      $g $f;

// Whole full-subcategory inclusion into the ambient functor category.
injective symbol strict_functor_include_func
  (A B : Cat)
  : τ (Functor
      (@StrictFunctor_cat A B)
      (@Functor_cat A B));

rule @fapp0 _ _ (@strict_functor_include_func $A $B) $X
  ↪ @strict_functor $A $B $X;

// The profile is full on the reused ambient transformation homs.
rule @fapp1_func _ _
      (@strict_functor_include_func $A $B) $X $Y
  ↪ @id_func
      (@Transf_cat
        $A $B
        (@strict_functor $A $B $X)
        (@strict_functor $A $B $Y));

// Integration's separately probed full-subcategory inclusion projection.
rule @fapp1_fapp0 _ _ (@strict_functor_include_func _ _) _ _ $epsilon
  ↪ $epsilon;

// -----------------------------------------------------------------------------------------------
// Whole strict-transfor property and stable ambient view
// -----------------------------------------------------------------------------------------------

// Whole post/left source of an ordinary transformation's intrinsic naturality
// cell. This is a readable alias of the existing displayed internal action.
symbol strict_transfor_naturality_lhs_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (X : τ (Obj A))
  [Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  : τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z)))
≔ @functord_transport_lhs_func
    A
    (@hom_ A A (@id_func A) X)
    (@hom_ B A G (@fapp0 A B F X))
    (@tapp1_at_transf A B F G X epsilon)
    Y Z g;

// Whole post/left target of the same intrinsic naturality cell.
symbol strict_transfor_naturality_rhs_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (X : τ (Obj A))
  [Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  : τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z)))
≔ @functord_transport_rhs_func
    A
    (@hom_ A A (@id_func A) X)
    (@hom_ B A G (@fapp0 A B F X))
    (@tapp1_at_transf A B F G X epsilon)
    Y Z g;

// Existing whole post/left cell under its strict-profile reading.
symbol strict_transfor_naturality_transf
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (X : τ (Obj A))
  [Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  : τ (Transf
      (@strict_transfor_naturality_lhs_func
        A B F G epsilon X Y Z g)
      (@strict_transfor_naturality_rhs_func
        A B F G epsilon X Y Z g))
≔ @tapp1_post_laxity_transf
    A B F G epsilon X Y Z g;

// Post/left strictness is whole in the retained source arrow. The property
// constrains the existing cell and supplies no parallel naturality square.
symbol IsPostStrictTransfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  : Grpd
≔ @Pi_grpd
    (Obj A)
    (λ X : τ (Obj A),
      @Pi_grpd
        (Obj A)
        (λ Y : τ (Obj A),
          @Pi_grpd
            (Obj A)
            (λ Z : τ (Obj A),
              @Pi_grpd
                (Hom A Y Z)
                (λ g : τ (Hom A Y Z),
                  @IsStrictCell
                    (@Functor_cat
                      (Hom_cat A X Y)
                      (Hom_cat B
                        (@fapp0 A B F X)
                        (@fapp0 A B G Z)))
                    (@strict_transfor_naturality_lhs_func
                      A B F G epsilon X Y Z g)
                    (@strict_transfor_naturality_rhs_func
                      A B F G epsilon X Y Z g)
                    (@strict_transfor_naturality_transf
                      A B F G epsilon X Y Z g)))));

// Whole pre/right source, retaining q:X->Y while h:W->X is selected.
symbol strict_transfor_pre_naturality_lhs_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (Y : τ (Obj A))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  : τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
≔ @functord_transport_lhs_func
    (Op_cat A)
    (@hom_con A Y A (@id_func A))
    (@hom_con B (@fapp0 A B G Y) A F)
    (@tapp1_con_at_transf A B F G epsilon Y)
    X W h;

// Whole pre/right target of the same intrinsic cell.
symbol strict_transfor_pre_naturality_rhs_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (Y : τ (Obj A))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  : τ (Functor
      (Hom_cat A X Y)
      (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
≔ @functord_transport_rhs_func
    (Op_cat A)
    (@hom_con A Y A (@id_func A))
    (@hom_con B (@fapp0 A B G Y) A F)
    (@tapp1_con_at_transf A B F G epsilon Y)
    X W h;

// Existing whole pre/right cell under its strict-profile reading.
symbol strict_transfor_pre_naturality_transf
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (Y : τ (Obj A))
  [W X : τ (Obj A)]
  (h : τ (Hom A W X))
  : τ (Transf
      (@strict_transfor_pre_naturality_lhs_func
        A B F G epsilon Y W X h)
      (@strict_transfor_pre_naturality_rhs_func
        A B F G epsilon Y W X h))
≔ @tapp1_pre_laxity_transf
    A B F G epsilon Y W X h;

// Pre/right strictness is a second skew evidence family over the existing
// pre/right cell. It does not postulate a new cell.
symbol IsPreStrictTransfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  : Grpd
≔ @Pi_grpd
    (Obj A)
    (λ Y : τ (Obj A),
      @Pi_grpd
        (Obj A)
        (λ W : τ (Obj A),
          @Pi_grpd
            (Obj A)
            (λ X : τ (Obj A),
              @Pi_grpd
                (Hom A W X)
                (λ h : τ (Hom A W X),
                  @IsStrictCell
                    (@Functor_cat
                      (Hom_cat A X Y)
                      (Hom_cat B
                        (@fapp0 A B F W)
                        (@fapp0 A B G Y)))
                    (@strict_transfor_pre_naturality_lhs_func
                      A B F G epsilon Y W X h)
                    (@strict_transfor_pre_naturality_rhs_func
                      A B F G epsilon Y W X h)
                    (@strict_transfor_pre_naturality_transf
                      A B F G epsilon Y W X h)))));

// Full strictness carries evidence for both existing skew whole cells.
symbol IsStrictTransfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  : Grpd
≔ @Product_grpd
    (@IsPostStrictTransfor A B F G epsilon)
    (@IsPreStrictTransfor A B F G epsilon);

// Conventional orientation names: a lax square retains the post/left cell
// and makes the pre/right leg strict; oplax reverses that choice.
symbol IsLaxTransfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  : Grpd
≔ @IsPreStrictTransfor A B F G epsilon;

symbol IsOplaxTransfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  : Grpd
≔ @IsPostStrictTransfor A B F G epsilon;

/*
  Only the oplax property is active. An exact `OplaxTransfor` Sigma package,
  stable `oplax_transfor` ambient view, higher subcategory, and mirror Gray
  hom are deferred until a concrete consumer requires post/left computation
  while retaining the pre/right cell. Raw ambient transfors do not acquire
  that computation implicitly.
*/

// Opaque full-image classifier for conventional lax transfors. Admission
// evidence constrains the existing pre/right cell and is not projected.
injective symbol LaxTransfor
  [A B : Cat]
  (F G : τ (Functor A B))
  : Grpd;

// Admission constructor; deliberately non-injective so certificate choice is
// unobservable while the ambient carrier remains a unification obligation.
symbol make_lax_transfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (lax : τ (@IsLaxTransfor A B F G epsilon))
  : τ (@LaxTransfor A B F G);

// Stable conventional-lax ambient view. The profile head retains pre/right
// computation while leaving the post/left cell directed and observable.
injective symbol lax_transfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G))
  : τ (Transf F G);

// Explicit raw observation for consumers intentionally leaving the profile.
injective symbol lax_transfor_underlying
  [A B : Cat]
  [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G))
  : τ (Transf F G);

rule @lax_transfor_underlying _ _ _ _
      (@make_lax_transfor _ _ _ _ $epsilon _)
  ↪ $epsilon;

unif_rule
  @lax_transfor_underlying $A $B $F $G $L
  ≡ @lax_transfor $A $B $F $G $L
  ↪ [ tt ≡ tt ];

unif_rule
  @lax_transfor $A $B $F $G
    (@make_lax_transfor $A $B $F $G $epsilon _)
  ≡ $epsilon
  ↪ [ tt ≡ tt ];

unif_rule
  @make_lax_transfor $A $B $F $G $epsilon _
  ≡ @make_lax_transfor $A $B $F $G $theta _
  ↪ [ $epsilon ≡ $theta ];

// Transparent typed interface to the proof-time carrier comparison.
symbol make_lax_transfor_carrier_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (lax : τ (@IsLaxTransfor A B F G epsilon))
  : τ (@=
      (Transf F G)
      (@lax_transfor A B F G
        (@make_lax_transfor A B F G epsilon lax))
      epsilon)
≔ @eq_refl
    (Transf F G)
    (@lax_transfor A B F G
      (@make_lax_transfor A B F G epsilon lax));

// Full higher subcategory on conventional lax-transfor objects. Its higher
// homs are the existing ambient modifications and subsequent iterated cells.
injective symbol LaxTransfor_cat
  [A B : Cat]
  [F G : τ (Functor A B)]
  : Cat;

rule Obj (@LaxTransfor_cat $A $B $F $G)
  ↪ @LaxTransfor $A $B $F $G;

rule Hom_cat (@LaxTransfor_cat $A $B $F $G) $L $M
  ↪ Hom_cat
      (@Transf_cat $A $B $F $G)
      (@lax_transfor $A $B $F $G $L)
      (@lax_transfor $A $B $F $G $M);

// Whole inclusion of the profiled hom category into the ambient transfor
// category. Point and hom action only forget evidence; no cell is rebuilt.
injective symbol lax_transfor_include_func
  [A B : Cat]
  [F G : τ (Functor A B)]
  : τ (Functor
      (@LaxTransfor_cat A B F G)
      (@Transf_cat A B F G));

rule @fapp0 _ _ (@lax_transfor_include_func $A $B $F $G) $L
  ↪ @lax_transfor $A $B $F $G $L;

rule @fapp1_func _ _
      (@lax_transfor_include_func $A $B $F $G) $L $M
  ↪ @id_func
      (Hom_cat
        (@Transf_cat $A $B $F $G)
        (@lax_transfor $A $B $F $G $L)
        (@lax_transfor $A $B $F $G $M));

// Direct capped projection joins evaluation of the whole inclusion action.
rule @fapp1_fapp0 _ _
      (@lax_transfor_include_func _ _ _ _) _ _ $Theta
  ↪ $Theta;

// Gray internal hom: strict functor objects and conventional lax-transfor
// arrows. This is intentionally distinct from StrictFunctor_cat, whose homs
// contain every ambient transfor.
injective symbol GrayHom_lax
  (A B : Cat)
  : Cat;

rule Obj (@GrayHom_lax $A $B)
  ↪ @StrictFunctor $A $B;

rule Hom_cat (@GrayHom_lax $A $B) $S $T
  ↪ @LaxTransfor_cat
      $A $B
      (@strict_functor $A $B $S)
      (@strict_functor $A $B $T);

// Whole Gray-hom inclusion into the ambient functor category.
injective symbol grayhom_lax_include_func
  (A B : Cat)
  : τ (Functor
      (@GrayHom_lax A B)
      (@Functor_cat A B));

rule @fapp0 _ _ (@grayhom_lax_include_func $A $B) $S
  ↪ @strict_functor $A $B $S;

rule @fapp1_func _ _
      (@grayhom_lax_include_func $A $B) $S $T
  ↪ @lax_transfor_include_func
      $A $B
      (@strict_functor $A $B $S)
      (@strict_functor $A $B $T);

rule @fapp1_fapp0 _ _
      (@grayhom_lax_include_func $A $B) $S $T $L
  ↪ @lax_transfor
      $A $B
      (@strict_functor $A $B $S)
      (@strict_functor $A $B $T)
      $L;

// Whole pre/right naturality for the conventional lax profile. The
// post/left cell remains the retained directed comparison.
rule @comp_fapp0
      Cat_cat _ _ _
      (@hom_precomp_along_func
        $A $B $F (@fapp0 $A $B $G $Y) $W $X $h)
      (@tapp1_func
        $A $B $F $G $X $Y
        (@lax_transfor $A $B $F $G $L))
  ↪ @comp_fapp0
      Cat_cat _ _ _
      (@tapp1_func
        $A $B $F $G $W $Y
        (@lax_transfor $A $B $F $G $L))
      (@hom_precomp_along_func $A $A (@id_func $A) $Y $W $X $h);

// Capped pre/right naturality under the same one-sided profile.
rule @comp_fapp0
      $B _ _ _
      (@tapp1_fapp0
        $A $B $F $G $X $Y
        (@lax_transfor $A $B $F $G $L)
        $f)
      (@fapp1_fapp0 $A $B $F $W $X $h)
  ↪ @tapp1_fapp0
      $A $B $F $G $W $Y
      (@lax_transfor $A $B $F $G $L)
      (@comp_fapp0 $A $W $X $Y $f $h);

// Stable proof-time pre/right reading of the off-diagonal action.
unif_rule
  @tapp1_fapp0
    $A $B $F $G $X $Y
    (@lax_transfor $A $B $F $G $L)
    $g
  ≡ @hom_precomp_along_fapp0
      $B $B $IdB $GY $FX $FY $Fg $epsilonY
  ↪ [
    $IdB ≡ (@id Cat_cat $B);
    $GY ≡ (@fapp0 $A $B $G $Y);
    $FX ≡ (@fapp0 $A $B $F $X);
    $FY ≡ (@fapp0 $A $B $F $Y);
    $Fg ≡ (@fapp1_fapp0 $A $B $F $X $Y $g);
    $epsilonY ≡ (@tapp0_fapp0
      $A $B $F $G $Y
      (@lax_transfor $A $B $F $G $L))
  ];

// Cat-valued pre/right projection for the same profile.
rule @fapp0 _ _
      (@tapp0_fapp0
        $K Cat_cat $E $D $y
        (@lax_transfor $K Cat_cat $E $D $L))
      (@fapp0 _ _
        (@fapp1_fapp0 $K Cat_cat $E $x $y $p)
        $u)
  ↪ @fapp0 _ _
      (@tapp1_fapp0
        $K Cat_cat $E $D $x $y
        (@lax_transfor $K Cat_cat $E $D $L)
        $p)
      $u;

/*
  Exact whole-cell identity for the conventional lax profile.

  This mirrors the strict-functor compositor rule: the existing deep
  `fdapp1_comma_projection_transf` remains the semantic owner and computes to
  identity only when its transfor is viewed through `lax_transfor`.  The
  shared base K is inferred to the contravariant base from the stable
  tapp1_con owner; no reducible Op(A) pattern or parallel cell is introduced.
*/
rule @fdapp1_comma_projection_transf
      $K _ _
      (@tapp1_con_at_transf
        $A $B $F $G
        (@lax_transfor $A $B $F $G $L)
        $Y)
      (@fdapp1_int_transfd
        $K _ _
        (@tapp1_con_at_transf
          $A $B $F $G
          (@lax_transfor $A $B $F $G $L)
          $Y))
      $X $W $h
  ↪ @id
      (@Functor_cat
        (Hom_cat $A $X $Y)
        (Hom_cat
          $B
          (@fapp0 $A $B $F $W)
          (@fapp0 $A $B $G $Y)))
      (@strict_transfor_pre_naturality_lhs_func
        $A $B $F $G
        (@lax_transfor $A $B $F $G $L)
        $Y $W $X $h);

// Every classified lax object canonically satisfies its semantic property.
// Both fields compute by reflexivity; no admission certificate is recovered.
symbol lax_transfor_is_lax
  [A B : Cat]
  [F G : τ (Functor A B)]
  (L : τ (@LaxTransfor A B F G))
  : τ (@IsLaxTransfor A B F G (@lax_transfor A B F G L))
≔ λ Y : τ (Obj A),
  λ W : τ (Obj A),
  λ X : τ (Obj A),
  λ h : τ (Hom A W X),
    Struct_sigma
      (@eq_refl
        (Functor
          (Hom_cat A X Y)
          (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
        (@strict_transfor_pre_naturality_lhs_func
          A B F G (@lax_transfor A B F G L) Y W X h))
      (@eq_refl
        (Hom
          (@Functor_cat
            (Hom_cat A X Y)
            (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
          (@strict_transfor_pre_naturality_lhs_func
            A B F G (@lax_transfor A B F G L) Y W X h)
          (@strict_transfor_pre_naturality_rhs_func
            A B F G (@lax_transfor A B F G L) Y W X h))
        (@strict_transfor_pre_naturality_transf
          A B F G (@lax_transfor A B F G L) Y W X h));

symbol strict_transfor_strictness_intro
  [A B : Cat]
  [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (post : τ (@IsPostStrictTransfor A B F G epsilon))
  (pre : τ (@IsPreStrictTransfor A B F G epsilon))
  : τ (@IsStrictTransfor A B F G epsilon)
≔ @Product_pair_grpd
    (@IsPostStrictTransfor A B F G epsilon)
    (@IsPreStrictTransfor A B F G epsilon)
    post pre;

symbol strict_transfor_post_evidence
  [A B : Cat]
  [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (strict : τ (@IsStrictTransfor A B F G epsilon))
  : τ (@IsPostStrictTransfor A B F G epsilon)
≔ sigma_Fst strict;

symbol strict_transfor_pre_evidence
  [A B : Cat]
  [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (strict : τ (@IsStrictTransfor A B F G epsilon))
  : τ (@IsPreStrictTransfor A B F G epsilon)
≔ sigma_Snd strict;

// Evaluating a whole strict cell gives strictness of its existing component.
// This is a reusable projection theorem, not a second pointwise property.
symbol strict_cell_tapp0_evidence
  [K D : Cat]
  [F G : τ (Functor K D)]
  [theta : τ (Transf F G)]
  (e : τ (@IsStrictCell (@Functor_cat K D) F G theta))
  (x : τ (Obj K))
  : τ (@IsStrictCell
      D
      (@fapp0 K D F x)
      (@fapp0 K D G x)
      (@tapp0_fapp0 K D F G x theta))
≔ Struct_sigma
    (@eq_ap
      (Functor K D)
      (Obj D)
      (λ H : τ (Functor K D), @fapp0 K D H x)
      F G
      (@strict_cell_path (@Functor_cat K D) F G theta e))
    (@eq_trans
      (Hom D (@fapp0 K D F x) (@fapp0 K D G x))
      (@tapp0_fapp0 K D F G x theta)
      (@tapp0_fapp0
        K D F G x
        (@path_to_hom
          (@Functor_cat K D) F G
          (@strict_cell_path (@Functor_cat K D) F G theta e)))
      (@path_to_hom
        D
        (@fapp0 K D F x)
        (@fapp0 K D G x)
        (@eq_ap
          (Functor K D)
          (Obj D)
          (λ H : τ (Functor K D), @fapp0 K D H x)
          F G
          (@strict_cell_path (@Functor_cat K D) F G theta e)))
      (@eq_ap
        (Hom (@Functor_cat K D) F G)
        (Hom D (@fapp0 K D F x) (@fapp0 K D G x))
        (λ alpha : τ (Hom (@Functor_cat K D) F G),
          @tapp0_fapp0 K D F G x alpha)
        theta
        (@path_to_hom
          (@Functor_cat K D) F G
          (@strict_cell_path (@Functor_cat K D) F G theta e))
        (@strict_cell_agreement (@Functor_cat K D) F G theta e))
      (@tapp0_path_to_hom
        K D F G
        (@strict_cell_path (@Functor_cat K D) F G theta e)
        x));

// Public capped evidence, obtained by evaluating the whole property at f.
symbol strict_transfor_naturality_evidence
  [A B : Cat]
  [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (strict : τ (@IsStrictTransfor A B F G epsilon))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
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
      (@tapp1_post_laxity_cell A B F G epsilon X Y Z g f))
≔ @strict_cell_tapp0_evidence
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z))
    (@strict_transfor_naturality_lhs_func
      A B F G epsilon X Y Z g)
    (@strict_transfor_naturality_rhs_func
      A B F G epsilon X Y Z g)
    (@strict_transfor_naturality_transf
      A B F G epsilon X Y Z g)
    ((@strict_transfor_post_evidence A B F G epsilon strict) X Y Z g)
    f;

// Capped pre/right evidence for the one-sided lax-arrow profile.
symbol pre_strict_transfor_naturality_evidence
  [A B : Cat]
  [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (pre : τ (@IsPreStrictTransfor A B F G epsilon))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X))
  (q : τ (Hom A X Y))
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
      (@tapp1_pre_laxity_cell A B F G epsilon W X Y h q))
≔ @strict_cell_tapp0_evidence
    (Hom_cat A X Y)
    (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y))
    (@strict_transfor_pre_naturality_lhs_func
      A B F G epsilon Y W X h)
    (@strict_transfor_pre_naturality_rhs_func
      A B F G epsilon Y W X h)
    (@strict_transfor_pre_naturality_transf
      A B F G epsilon Y W X h)
    (pre Y W X h)
    q;

// Public full-strict reading delegates to the pre/right evidence projection.
symbol strict_transfor_pre_naturality_evidence
  [A B : Cat]
  [F G : τ (Functor A B)]
  [epsilon : τ (Transf F G)]
  (strict : τ (@IsStrictTransfor A B F G epsilon))
  [W X Y : τ (Obj A)]
  (h : τ (Hom A W X))
  (q : τ (Hom A X Y))
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
      (@tapp1_pre_laxity_cell A B F G epsilon W X Y h q))
≔ @pre_strict_transfor_naturality_evidence
    A B F G epsilon
    (@strict_transfor_pre_evidence A B F G epsilon strict)
    W X Y h q;

// Opaque full-image classifier for full strict transfors.
injective symbol StrictTransfor
  [A B : Cat]
  (F G : τ (Functor A B))
  : Grpd;

// Admission constructor; evidence choice is not observable.
symbol make_strict_transfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  : τ (@StrictTransfor A B F G);

// Stable full-strict ambient view.
injective symbol strict_transfor
  [A B : Cat]
  [F G : τ (Functor A B)]
  (U : τ (@StrictTransfor A B F G))
  : τ (Transf F G);

// Explicit raw observation.
injective symbol strict_transfor_underlying
  [A B : Cat]
  [F G : τ (Functor A B)]
  (U : τ (@StrictTransfor A B F G))
  : τ (Transf F G);

rule @strict_transfor_underlying _ _ _ _
      (@make_strict_transfor _ _ _ _ $epsilon _)
  ↪ $epsilon;

unif_rule
  @strict_transfor_underlying $A $B $F $G $U
  ≡ @strict_transfor $A $B $F $G $U
  ↪ [ tt ≡ tt ];

unif_rule
  @strict_transfor $A $B $F $G
    (@make_strict_transfor $A $B $F $G $epsilon _)
  ≡ $epsilon
  ↪ [ tt ≡ tt ];

unif_rule
  @make_strict_transfor $A $B $F $G $epsilon _
  ≡ @make_strict_transfor $A $B $F $G $theta _
  ↪ [ $epsilon ≡ $theta ];

// Transparent typed carrier comparison.
symbol make_strict_transfor_carrier_path
  [A B : Cat]
  [F G : τ (Functor A B)]
  (epsilon : τ (Transf F G))
  (p : τ (@IsStrictTransfor A B F G epsilon))
  : τ (@=
      (Transf F G)
      (@strict_transfor A B F G
        (@make_strict_transfor A B F G epsilon p))
      epsilon)
≔ @eq_refl
    (Transf F G)
    (@strict_transfor A B F G
      (@make_strict_transfor A B F G epsilon p));

// Whole post/left strict naturality guarded by the evidence-bearing view.
// The represented source endpoint is inferred so the rule also matches after
// the literal F[X] endpoint has reduced.
rule @comp_fapp0
      Cat_cat _ _ _
      (@hom_postcomp_func $B $A $G _ $Y $Z $g)
      (@tapp1_func
        $A $B $F $G $X $Y
        (@strict_transfor $A $B $F $G $U))
  ↪ @comp_fapp0
      Cat_cat _ _ _
      (@tapp1_func
        $A $B $F $G $X $Z
        (@strict_transfor $A $B $F $G $U))
      (@hom_postcomp_func $A $A (@id_func $A) $X $Y $Z $g);

// Capped post/left naturality guarded by the same profile.
rule @comp_fapp0
      $B _ _ _
      (@fapp1_fapp0 $A $B $G $Y $Z $g)
      (@tapp1_fapp0
        $A $B $F $G $X $Y
        (@strict_transfor $A $B $F $G $U)
        $f)
  ↪ @tapp1_fapp0
      $A $B $F $G $X $Z
      (@strict_transfor $A $B $F $G $U)
      (@comp_fapp0 $A $X $Y $Z $g $f);

// Profile-guarded proof-time post/left reading of the off-diagonal action.
unif_rule
  @tapp1_fapp0
    $A $B $F $G $X $Y
    (@strict_transfor $A $B $F $G $U)
    $g
  ≡ @hom_postcomp_fapp0
      $B $B $IdB $FX $GX $GY $Gg $epsilonX
  ↪ [
    $IdB ≡ (@id Cat_cat $B);
    $FX ≡ (@fapp0 $A $B $F $X);
    $GX ≡ (@fapp0 $A $B $G $X);
    $GY ≡ (@fapp0 $A $B $G $Y);
    $Gg ≡ (@fapp1_fapp0 $A $B $G $X $Y $g);
    $epsilonX ≡ (@tapp0_fapp0
      $A $B $F $G $X
      (@strict_transfor $A $B $F $G $U))
  ];

// Cat-valued post/left projection guarded by the strict-transfor view.
rule @fapp0 _ _
      (@fapp1_fapp0 $K Cat_cat $D $x $y $p)
      (@fapp0 _ _
        (@tapp0_fapp0
          $K Cat_cat $E $D $x
          (@strict_transfor $K Cat_cat $E $D $U))
        $u)
  ↪ @fapp0 _ _
      (@tapp1_fapp0
        $K Cat_cat $E $D $x $y
        (@strict_transfor $K Cat_cat $E $D $U)
        $p)
      $u;

// Whole pre/right strict naturality guarded by the same full profile.
rule @comp_fapp0
      Cat_cat _ _ _
      (@hom_precomp_along_func
        $A $B $F (@fapp0 $A $B $G $Y) $W $X $h)
      (@tapp1_func
        $A $B $F $G $X $Y
        (@strict_transfor $A $B $F $G $U))
  ↪ @comp_fapp0
      Cat_cat _ _ _
      (@tapp1_func
        $A $B $F $G $W $Y
        (@strict_transfor $A $B $F $G $U))
      (@hom_precomp_along_func $A $A (@id_func $A) $Y $W $X $h);

// Capped pre/right naturality under the evidence-bearing view.
rule @comp_fapp0
      $B _ _ _
      (@tapp1_fapp0
        $A $B $F $G $X $Y
        (@strict_transfor $A $B $F $G $U)
        $f)
      (@fapp1_fapp0 $A $B $F $W $X $h)
  ↪ @tapp1_fapp0
      $A $B $F $G $W $Y
      (@strict_transfor $A $B $F $G $U)
      (@comp_fapp0 $A $W $X $Y $f $h);

// Profile-guarded proof-time pre/right reading of off-diagonal action.
unif_rule
  @tapp1_fapp0
    $A $B $F $G $X $Y
    (@strict_transfor $A $B $F $G $U)
    $g
  ≡ @hom_precomp_along_fapp0
      $B $B $IdB $GY $FX $FY $Fg $epsilonY
  ↪ [
    $IdB ≡ (@id Cat_cat $B);
    $GY ≡ (@fapp0 $A $B $G $Y);
    $FX ≡ (@fapp0 $A $B $F $X);
    $FY ≡ (@fapp0 $A $B $F $Y);
    $Fg ≡ (@fapp1_fapp0 $A $B $F $X $Y $g);
    $epsilonY ≡ (@tapp0_fapp0
      $A $B $F $G $Y
      (@strict_transfor $A $B $F $G $U))
  ];

// Cat-valued pre/right projection guarded by the strict-transfor view.
rule @fapp0 _ _
      (@tapp0_fapp0
        $K Cat_cat $E $D $y
        (@strict_transfor $K Cat_cat $E $D $U))
      (@fapp0 _ _
        (@fapp1_fapp0 $K Cat_cat $E $x $y $p)
        $u)
  ↪ @fapp0 _ _
      (@tapp1_fapp0
        $K Cat_cat $E $D $x $y
        (@strict_transfor $K Cat_cat $E $D $U)
        $p)
      $u;

// Exact post/left whole-cell identity under the full strict profile.
rule @fdapp1_comma_projection_transf
      $A _ _
      (@tapp1_at_transf
        $A $B $F $G $X
        (@strict_transfor $A $B $F $G $U))
      (@fdapp1_int_transfd
        $A _ _
        (@tapp1_at_transf
          $A $B $F $G $X
          (@strict_transfor $A $B $F $G $U)))
      $Y $Z $g
  ↪ @id
      (@Functor_cat
        (Hom_cat $A $X $Y)
        (Hom_cat
          $B
          (@fapp0 $A $B $F $X)
          (@fapp0 $A $B $G $Z)))
      (@strict_transfor_naturality_lhs_func
        $A $B $F $G
        (@strict_transfor $A $B $F $G $U)
        $X $Y $Z $g);

// Exact pre/right whole-cell identity reuses the stable contravariant owner.
rule @fdapp1_comma_projection_transf
      $K _ _
      (@tapp1_con_at_transf
        $A $B $F $G
        (@strict_transfor $A $B $F $G $U)
        $Y)
      (@fdapp1_int_transfd
        $K _ _
        (@tapp1_con_at_transf
          $A $B $F $G
          (@strict_transfor $A $B $F $G $U)
          $Y))
      $X $W $h
  ↪ @id
      (@Functor_cat
        (Hom_cat $A $X $Y)
        (Hom_cat
          $B
          (@fapp0 $A $B $F $W)
          (@fapp0 $A $B $G $Y)))
      (@strict_transfor_pre_naturality_lhs_func
        $A $B $F $G
        (@strict_transfor $A $B $F $G $U)
        $Y $W $X $h);

// Canonical full strictness over the two existing skew whole cells.
symbol strict_transfor_is_strict
  [A B : Cat]
  [F G : τ (Functor A B)]
  (U : τ (@StrictTransfor A B F G))
  : τ (@IsStrictTransfor A B F G
      (@strict_transfor A B F G U))
≔ @strict_transfor_strictness_intro
    A B F G
    (@strict_transfor A B F G U)
    (λ X : τ (Obj A),
      λ Y : τ (Obj A),
      λ Z : τ (Obj A),
      λ g : τ (Hom A Y Z),
        Struct_sigma
          (@eq_refl
            (Functor
              (Hom_cat A X Y)
              (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z)))
            (@strict_transfor_naturality_lhs_func
              A B F G (@strict_transfor A B F G U) X Y Z g))
          (@eq_refl
            (Hom
              (@Functor_cat
                (Hom_cat A X Y)
                (Hom_cat B (@fapp0 A B F X) (@fapp0 A B G Z)))
              (@strict_transfor_naturality_lhs_func
                A B F G (@strict_transfor A B F G U) X Y Z g)
              (@strict_transfor_naturality_rhs_func
                A B F G (@strict_transfor A B F G U) X Y Z g))
            (@strict_transfor_naturality_transf
              A B F G (@strict_transfor A B F G U) X Y Z g)))
    (λ Y : τ (Obj A),
      λ W : τ (Obj A),
      λ X : τ (Obj A),
      λ h : τ (Hom A W X),
        Struct_sigma
          (@eq_refl
            (Functor
              (Hom_cat A X Y)
              (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
            (@strict_transfor_pre_naturality_lhs_func
              A B F G (@strict_transfor A B F G U) Y W X h))
          (@eq_refl
            (Hom
              (@Functor_cat
                (Hom_cat A X Y)
                (Hom_cat B (@fapp0 A B F W) (@fapp0 A B G Y)))
              (@strict_transfor_pre_naturality_lhs_func
                A B F G (@strict_transfor A B F G U) Y W X h)
              (@strict_transfor_pre_naturality_rhs_func
                A B F G (@strict_transfor A B F G U) Y W X h))
            (@strict_transfor_pre_naturality_transf
              A B F G (@strict_transfor A B F G U) Y W X h)));

/* API-04V: vertical accumulation is profile-specific. The left formula
   requires the later transfor's pre/right profile; the right formula needs
   the earlier transfor's post/left profile. Full-strict views provide both.
   The outer codomain B is a real ambient-composition guard: coincident
   Hom types in another presentation do not identify its composition owner.
   No opaque oplax classifier is introduced for this bounded migration. */

// Later lax_transfor view supplies the pre/right leg.
rule @comp_fapp0 $B _ _ _
      (@tapp0_fapp0 _ _ _ _ $Y (@lax_transfor $A $B $G $H $V))
      (@tapp1_fapp0 $A $B $F $G $X $Y $epsilon $f)
  ↪ @tapp1_fapp0 $A $B $F $H $X $Y
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H (@lax_transfor $A $B $G $H $V) $epsilon) $f;

// Later strict_transfor view supplies the pre/right leg.
rule @comp_fapp0 $B _ _ _
      (@tapp0_fapp0 _ _ _ _ $Y (@strict_transfor $A $B $G $H $V))
      (@tapp1_fapp0 $A $B $F $G $X $Y $epsilon $f)
  ↪ @tapp1_fapp0 $A $B $F $H $X $Y
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H (@strict_transfor $A $B $G $H $V) $epsilon) $f;

// Earlier full-strict view supplies the post/left leg.
rule @comp_fapp0 $B _ _ _
      (@tapp1_fapp0 $A $B $G $H $X $Y $eta $f)
      (@tapp0_fapp0 _ _ _ _ $X (@strict_transfor $A $B $F $G $U))
  ↪ @tapp1_fapp0 $A $B $F $H $X $Y
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H $eta (@strict_transfor $A $B $F $G $U)) $f;

// Both legs for simultaneous accumulation of p and q.
rule @comp_fapp0 $B _ _ _
      (@tapp1_fapp0 _ _ _ _ $Y $Z (@lax_transfor $A $B $G $H $V) $q)
      (@tapp1_fapp0 _ _ _ _ $X $Y (@strict_transfor $A $B $F $G $U) $p)
  ↪ @tapp1_fapp0 $A $B $F $H $X $Z
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H (@lax_transfor $A $B $G $H $V) (@strict_transfor $A $B $F $G $U))
      (@comp_fapp0 $A $X $Y $Z $q $p);

// Both legs for simultaneous accumulation of p and q.
rule @comp_fapp0 $B _ _ _
      (@tapp1_fapp0 _ _ _ _ $Y $Z (@strict_transfor $A $B $G $H $V) $q)
      (@tapp1_fapp0 _ _ _ _ $X $Y (@strict_transfor $A $B $F $G $U) $p)
  ↪ @tapp1_fapp0 $A $B $F $H $X $Z
      (@comp_fapp0 (Functor_cat $A $B) $F $G $H (@strict_transfor $A $B $G $H $V) (@strict_transfor $A $B $F $G $U))
      (@comp_fapp0 $A $X $Y $Z $q $p);

// -----------------------------------------------------------------------------------------------
// Strict displayed-functor profile over the existing directed laxity cell
// -----------------------------------------------------------------------------------------------

// Strictness constrains the public whole-in-fibre-object cell at every base
// arrow; it does not store a second naturality transformation.
symbol IsStrictFunctord
  [K : Cat]
  [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ x : τ (Obj K),
      @Pi_grpd
        (Obj K)
        (λ y : τ (Obj K),
          @Pi_grpd
            (Hom K x y)
            (λ p : τ (Hom K x y),
              @IsStrictCell
                (@Functor_cat
                  (Fibre_cat E x)
                  (Fibre_cat D y))
                (@functord_transport_lhs_func K E D FF x y p)
                (@functord_transport_rhs_func K E D FF x y p)
                (@functord_laxity_transf K E D FF x y p))));

// Opaque full-image classifier for strict displayed functors.
injective symbol StrictFunctord
  [K : Cat]
  (E D : τ (Catd K))
  : Grpd;

// Admission constructor; evidence choice is not observable.
symbol make_strict_functord
  [K : Cat]
  [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF))
  : τ (@StrictFunctord K E D);

// Stable strict displayed-functor view.
injective symbol strict_functord
  [K : Cat]
  [E D : τ (Catd K)]
  (S : τ (@StrictFunctord K E D))
  : τ (Functord E D);

// Explicit raw observation.
injective symbol strict_functord_underlying
  [K : Cat]
  [E D : τ (Catd K)]
  (S : τ (@StrictFunctord K E D))
  : τ (Functord E D);

rule @strict_functord_underlying _ _ _
      (@make_strict_functord _ _ _ $FF _)
  ↪ $FF;

unif_rule
  @strict_functord_underlying $K $E $D $S
  ≡ @strict_functord $K $E $D $S
  ↪ [ tt ≡ tt ];

unif_rule
  @strict_functord $K $E $D
    (@make_strict_functord $K $E $D $FF _)
  ≡ $FF
  ↪ [ tt ≡ tt ];

unif_rule
  @make_strict_functord $K $E $D $FF _
  ≡ @make_strict_functord $K $E $D $GG _
  ↪ [ $FF ≡ $GG ];

// Transparent typed carrier comparison.
symbol make_strict_functord_carrier_path
  [K : Cat]
  [E D : τ (Catd K)]
  (FF : τ (Functord E D))
  (p : τ (@IsStrictFunctord K E D FF))
  : τ (@=
      (Functord E D)
      (@strict_functord K E D
        (@make_strict_functord K E D FF p))
      FF)
≔ @eq_refl
    (Functord E D)
    (@strict_functord K E D
      (@make_strict_functord K E D FF p));

// Capped strictness is component evaluation of the existing whole cell.
symbol strict_functord_laxity_evidence
  [K : Cat]
  [E D : τ (Catd K)]
  [FF : τ (Functord E D)]
  (strict : τ (@IsStrictFunctord K E D FF))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  (u : τ (Obj (Fibre_cat E x)))
  : τ (@IsStrictCell
      (Fibre_cat D y)
      (@fapp0
        (Fibre_cat E x) (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y p) u)
      (@fapp0
        (Fibre_cat E x) (Fibre_cat D y)
        (@functord_transport_rhs_func K E D FF x y p) u)
      (@tapp0_fapp0
        (Fibre_cat E x) (Fibre_cat D y)
        (@functord_transport_lhs_func K E D FF x y p)
        (@functord_transport_rhs_func K E D FF x y p)
        u
        (@functord_laxity_transf K E D FF x y p)))
≔ @strict_cell_tapp0_evidence
    (Fibre_cat E x)
    (Fibre_cat D y)
    (@functord_transport_lhs_func K E D FF x y p)
    (@functord_transport_rhs_func K E D FF x y p)
    (@functord_laxity_transf K E D FF x y p)
    (strict x y p)
    u;

// Profile-guarded whole target/right reading. The left/source reading remains
// the ambient lax action because it is the source of functord_laxity_transf.
unif_rule
  @tapp1_func
    $K Cat_cat $E $D $x $y
    (@strict_functord $K $E $D $S)
  ≡ @comp_fapp0 Cat_cat _ _ _
    (@hom_postcomp_func
      Cat_cat Cat_cat (@id Cat_cat Cat_cat)
      _ _ _
      (@tapp0_fapp0
        $K Cat_cat $E $D $y
        (@strict_functord $K $E $D $S)))
    (@fapp1_func $K Cat_cat $E $x $y)
  ↪ [ tt ≡ tt ];

// Stable capped target/right reading for the same profile.
unif_rule
  @tapp1_fapp0
    $K Cat_cat $E $D $x $y
    (@strict_functord $K $E $D $S)
    $p
  ≡ @comp_fapp0 Cat_cat _ _ _
      (@tapp0_fapp0
        $K Cat_cat $E $D $y
        (@strict_functord $K $E $D $S))
      (@fapp1_fapp0 $K Cat_cat $E $x $y $p)
  ↪ [ tt ≡ tt ];

symbol strict_functord_transport_rhs_tele_path
  [K : Cat]
  [E D : τ (Catd K)]
  (S : τ (@StrictFunctord K E D))
  (x y : τ (Obj K))
  : τ (@=
      (Functor
        (Hom_cat K x y)
        (Functor_cat (Fibre_cat E x) (Fibre_cat D y)))
      (@tapp1_func K Cat_cat E D x y
        (@strict_functord K E D S))
      (@functord_transport_rhs_tele_func
        K E D (@strict_functord K E D S) x y))
≔ @eq_refl
    (Functor
      (Hom_cat K x y)
      (Functor_cat (Fibre_cat E x) (Fibre_cat D y)))
    (@tapp1_func K Cat_cat E D x y
      (@strict_functord K E D S));

symbol strict_functord_transport_rhs_path
  [K : Cat]
  [E D : τ (Catd K)]
  (S : τ (@StrictFunctord K E D))
  [x y : τ (Obj K)]
  (p : τ (Hom K x y))
  : τ (@=
      (Functor (Fibre_cat E x) (Fibre_cat D y))
      (@tapp1_fapp0 K Cat_cat E D x y
        (@strict_functord K E D S) p)
      (@functord_transport_rhs_func
        K E D (@strict_functord K E D S) x y p))
≔ @eq_refl
    (Functor (Fibre_cat E x) (Fibre_cat D y))
    (@tapp1_fapp0 K Cat_cat E D x y
      (@strict_functord K E D S) p);
