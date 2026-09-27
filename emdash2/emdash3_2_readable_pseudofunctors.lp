/*
  Emdash v3.2: readable pseudofunctor property over ambient functor carriers.

  The active generic functor/transfor calculus exposes normal-lax compositor
  cells at formal internal-action endpoints. Consumers such as intrinsic
  cubical arrows require an invertible readable view of the existing
  compositor; its selected omega-equivalence inverse supplies the opposite
  boundary direction.

  IsPseudoFunctor is the direct dependent property of an already-existing
  Functor carrier. It does not supply another compositor: fixed-forward
  `OmegaEquivAlong` gives native equality-valued inverse data for the existing
  post cell extracted from internal action. Higher coherence remains the next
  internal action. No property wrapper, rule, or proof-time unifier is added.

  This capability is evidence over an already-existing ambient Functor; it is
  not a separate lax-carrier classifier. The former whole ambient
  functoriality cuts are retired: two direct endpoint paths now expose
  `F[g] o F[f]` and `F[g o f]` without identifying them. The remaining capped
  and naturality migrations are separate owner families.
*/

require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_path_pseudo_laxity;

symbol readable_pseudo_post_raw_source
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Obj (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
≔ @hom_postcomp_fapp0
    B B (@id_func B)
    (@fapp0 A B F X)
    (@fapp0 A B F Y)
    (@fapp0 A B F Z)
    (@fapp1_fapp0 A B F Y Z g)
    (@fapp1_fapp0 A B F X Y f);

symbol readable_pseudo_post_raw_target
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Obj (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
≔ @fapp1_fapp0 A B F X Z (@comp_fapp0 A X Y Z g f);

symbol readable_pseudo_post_stable_action
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Obj (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
≔ @fapp1_fapp0 A B F X Z
    (@hom_postcomp_fapp0 A A (@id_func A) X Y Z g f);

/*
  Direct endpoint observations after whole ambient functoriality migration.

  The intrinsic source is the general postcomposition owner
  `postcomp_F(g)(F[f])`; the rigid proof-time bridge compares it directly with
  the identity-family spelling of `F[g] o F[f]`. The intrinsic target is
  `F[postcomp_id(g)(f)]`; equality action on the existing source-category
  postcomposition path compares it with `F[g o f]`. Neither path identifies
  those two endpoints with each other.
*/

symbol readable_pseudo_post_stable_comp_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_stable_action A B F X Y Z g f)
      (@readable_pseudo_post_raw_target A B F X Y Z g f))
≔ @eq_ap
    (Hom A X Z)
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (λ r : τ (Hom A X Z), @fapp1_fapp0 A B F X Z r)
    (@hom_postcomp_fapp0 A A (@id_func A) X Y Z g f)
    (@comp_fapp0 A X Y Z g f)
    (@path_pseudo_laxity_postcomp_comp_path
      A A (@id_func A) X Y Z g f);

symbol readable_pseudo_post_source_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@readable_pseudo_post_raw_source A B F X Y Z g f))
≔ @eq_refl
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@strict_functor_compositor_lhs A B F X Y Z g f);

symbol readable_pseudo_post_target_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@readable_pseudo_post_raw_target A B F X Y Z g f))
≔ @readable_pseudo_post_stable_comp_path A B F X Y Z g f;

protected symbol readable_pseudo_post_source_reframe
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@strict_functor_compositor_lhs A B F X Y Z g f))
≔ @path_to_hom
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@readable_pseudo_post_raw_source A B F X Y Z g f)
    (@strict_functor_compositor_lhs A B F X Y Z g f)
    (@eq_sym
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@readable_pseudo_post_source_path A B F X Y Z g f));

protected symbol readable_pseudo_post_target_reframe
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@readable_pseudo_post_raw_target A B F X Y Z g f))
≔ @path_to_hom
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@strict_functor_compositor_rhs A B F X Y Z g f)
    (@readable_pseudo_post_raw_target A B F X Y Z g f)
    (@readable_pseudo_post_target_path A B F X Y Z g f);

// Readable post/left cell obtained only by reframing the existing internal
// compositor. No independent coherence cell is declared.
symbol readable_pseudo_post_cell
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@readable_pseudo_post_raw_target A B F X Y Z g f))
≔ @comp_fapp0
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@readable_pseudo_post_raw_source A B F X Y Z g f)
    (@strict_functor_compositor_rhs A B F X Y Z g f)
    (@readable_pseudo_post_raw_target A B F X Y Z g f)
    (@readable_pseudo_post_target_reframe A B F X Y Z g f)
    (@comp_fapp0
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@fapp1_compositor A B F X Y Z g f)
      (@readable_pseudo_post_source_reframe A B F X Y Z g f));

// Pre/right readable source for the same composite.
symbol readable_pseudo_pre_raw_source
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Obj (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z)))
≔ @hom_precomp_along_fapp0
    B B (@id_func B)
    (@fapp0 B B (@id_func B) (@fapp0 A B F Z))
    (@fapp0 A B F X)
    (@fapp0 A B F Y)
    (@fapp1_fapp0 A B F X Y f)
    (@fapp1_fapp0 A B F Y Z g);

// Existing proof-time post/pre comparison, now retained as first-class path.
symbol readable_pseudo_post_pre_source_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@readable_pseudo_pre_raw_source A B F X Y Z g f))
≔ @eq_refl
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@readable_pseudo_post_raw_source A B F X Y Z g f);

protected symbol readable_pseudo_post_pre_reframe
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@readable_pseudo_pre_raw_source A B F X Y Z g f))
≔ @path_to_hom
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@readable_pseudo_post_raw_source A B F X Y Z g f)
    (@readable_pseudo_pre_raw_source A B F X Y Z g f)
    (@readable_pseudo_post_pre_source_path A B F X Y Z g f);

// Normal-pseudofunctor property: every existing readable compositor is a
// fixed-forward native omega-equivalence. Identity preservation remains the
// current ambient normal-lax convention.
symbol IsPseudoFunctor
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
                  @Pi_grpd
                    (Hom A X Y)
                    (λ f : τ (Hom A X Y),
                      @OmegaEquivAlong
                        (Hom_cat B
                          (@fapp0 A B F X)
                          (@fapp0 A B F Z))
                        _ _
                        (@readable_pseudo_post_cell
                          A B F X Y Z g f))))));

// Post/left readable compositor:
//   F[g] o F[f] ~= F[g o f]
// at the stable hom_postcomp owner used by source-varying hom families.
symbol pseudo_compositor_equiv
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@IsPseudoFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@OmegaEquivAlong
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      _ _
      (@readable_pseudo_post_cell A B F X Y Z g f))
≔ P X Y Z g f;

// Pre/right reverse adjustment uses the selected left inverse of the one
// fixed-forward post cell, followed by the existing post/pre endpoint reframe.
// The `OmegaEquivAlong` right inverse and both cancellation laws remain
// available to later coherence consumers.
symbol pseudo_pre_inverse
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@IsPseudoFunctor A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (Hom
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_target A B F X Y Z g f)
      (@readable_pseudo_pre_raw_source A B F X Y Z g f))
≔ @comp_fapp0
    (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@readable_pseudo_post_raw_target A B F X Y Z g f)
    (@readable_pseudo_post_raw_source A B F X Y Z g f)
    (@readable_pseudo_pre_raw_source A B F X Y Z g f)
    (@readable_pseudo_post_pre_reframe A B F X Y Z g f)
    (@omega_equiv_along_left_inv
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      _ _
      (@readable_pseudo_post_cell A B F X Y Z g f)
      (@pseudo_compositor_equiv A B F P X Y Z g f));

// Supplied identity proof. Constructing it transparently requires the
// extracted unit/normality interface, which remains separate.
constant symbol identity_is_pseudo
  (A : Cat)
  : τ (@IsPseudoFunctor A A (@id_func A));

// Supplied composition proof. A transparent constructor requires the next
// internal action comparing the composite functor's intrinsic compositor with
// the two component properties.
constant symbol comp_is_pseudo
  [A B C : Cat]
  [F : τ (Functor A B)]
  (PF : τ (@IsPseudoFunctor A B F))
  [G : τ (Functor B C)]
  (PG : τ (@IsPseudoFunctor B C G))
  : τ (@IsPseudoFunctor
      A C (@comp_cat_fapp0 A B C G F));
