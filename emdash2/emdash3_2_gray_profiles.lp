/*
  Emdash v3.2: whole strict-functor evidence and an opaque strict classifier.

  StrictFunctor admits a coherent ambient carrier with whole IsStrictFunctor
  evidence. Stable classified action and explicit raw observation are distinct;
  canonical strictness is reconstructed from the existing compositor owner.
  The full StrictFunctor_cat reuses ambient transfors and their higher action.

  Integration boundary: the core's global composition/naturality cuts and
  GrayHom_lax's ambient-transfor homs remain until their consumer migrations.
  Their presence does not qualify ambient lax noncollapse or the final Gray
  arrow profile. The living action-profile integration plan owns that work.
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

// Capped projection beta for the full-subcategory inclusion. The generic
// fapp0(fapp1_func(...)) cut can hide the whole identity action before it
// reduces. Both projection orders return the same ambient transfor.
rule @fapp1_fapp0 _ _ (@strict_functor_include_func _ _) _ _ $epsilon
  ↪ $epsilon;

// Strict-object/lax-arrow right-hom profile.
injective symbol GrayHom_lax
  (A B : Cat)
  : Cat;

rule Obj (@GrayHom_lax $A $B)
  ↪ @StrictFunctor $A $B;

rule Hom_cat (@GrayHom_lax $A $B) $X $Y
  ↪ @Transf_cat
      $A $B
      (@strict_functor $A $B $X)
      (@strict_functor $A $B $Y);

// Identity delegates to the ambient functor category.
rule @id (@GrayHom_lax $A $B) $X
  ↪ @id
      (@Functor_cat $A $B)
      (@strict_functor $A $B $X);

// Composition delegates to the ambient functor category.
// lhs-audit: keep 2,3,4 -- the carrier projections occur on the RHS.
rule @comp_fapp0
      (@GrayHom_lax $A $B) $X $Y $Z $g $f
  ↪ @comp_fapp0
      (@Functor_cat $A $B)
      (@strict_functor $A $B $X)
      (@strict_functor $A $B $Y)
      (@strict_functor $A $B $Z)
      $g $f;

// Whole inclusion into the shared ambient functor category.
injective symbol grayhom_lax_include_func
  (A B : Cat)
  : τ (Functor
      (@GrayHom_lax A B)
      (@Functor_cat A B));

rule @fapp0 _ _ (@grayhom_lax_include_func $A $B) $X
  ↪ @strict_functor $A $B $X;

// The profile is full on the reused ambient transformation homs.
rule @fapp1_func _ _
      (@grayhom_lax_include_func $A $B) $X $Y
  ↪ @id_func
      (@Transf_cat
        $A $B
        (@strict_functor $A $B $X)
        (@strict_functor $A $B $Y));
