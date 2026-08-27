/*
  Emdash v3.2: readable pseudofunctor profiles over ambient functor carriers.

  The active generic functor/transfor calculus exposes normal-lax compositor
  cells at formal internal-action endpoints. Consumers such as intrinsic
  cubical arrows require an invertible readable view of the existing
  compositor; its selected omega-equivalence inverse supplies the opposite
  boundary direction.

  ReadablePseudoFunctorProfile is an abstract coherent capability indexed by
  its already-existing Functor carrier. It does not supply another compositor:
  fixed-forward `OmegaEquivAlong` gives native equality-valued inverse data
  for the existing post cell extracted from internal action. Higher coherence
  remains the next internal action. The only rewrite is the explicit profile
  constructor's field-projection beta; no proof-time unifier is added.

  This capability is evidence over an already-existing ambient Functor; it is
  not a separate lax-carrier classifier and does not disable the historical
  global strict cuts. Conversely, those temporary cuts must not be used to
  veto an intended lax consumer beta that otherwise passes its owner and
  subject-reduction checks; their migration remains profile-local future work.
*/

require open emdash.emdash3_2_gray_profiles;
require open emdash.emdash3_2_path_pseudo_laxity;

// Coherent readable pseudofunctor capability for one ambient carrier.
injective symbol ReadablePseudoFunctorProfile
  [A B : Cat]
  (F : τ (Functor A B))
  : Grpd;

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
  Prototype endpoint adapter.

  The historical global strict-functoriality cut selects the stable action
  `F[g o f]` before the formal left endpoint can expose `F[g] o F[f]`.
  The path ladder below therefore returns through the typed equality view of
  that temporary cut and then the stable postcomposition owner. It reframes an
  already-extracted cell; it neither constructs the compositor nor claims that
  generic lax endpoints remain noncollapsed. A later profile-local strict-cut
  migration must replace this ladder by direct left/right internal-action
  observations.
*/

symbol readable_pseudo_post_formal_source_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_lhs A B F X Y Z g f)
      (@readable_pseudo_post_stable_action A B F X Y Z g f))
≔ @eq_refl
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@strict_functor_compositor_lhs A B F X Y Z g f);

symbol readable_pseudo_post_formal_target_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@strict_functor_compositor_rhs A B F X Y Z g f)
      (@readable_pseudo_post_stable_action A B F X Y Z g f))
≔ @eq_refl
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@strict_functor_compositor_rhs A B F X Y Z g f);

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

symbol readable_pseudo_post_comp_raw_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_raw_target A B F X Y Z g f)
      (@comp_fapp0
        B
        (@fapp0 A B F X)
        (@fapp0 A B F Y)
        (@fapp0 A B F Z)
        (@fapp1_fapp0 A B F Y Z g)
        (@fapp1_fapp0 A B F X Y f)))
≔ @fapp1_comp_path A B F X Y Z g f;

symbol readable_pseudo_post_raw_owner_path
  [A B : Cat]
  (F : τ (Functor A B))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@=
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@comp_fapp0
        B
        (@fapp0 A B F X)
        (@fapp0 A B F Y)
        (@fapp0 A B F Z)
        (@fapp1_fapp0 A B F Y Z g)
        (@fapp1_fapp0 A B F X Y f))
      (@readable_pseudo_post_raw_source A B F X Y Z g f))
≔ @eq_sym
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@readable_pseudo_post_raw_source A B F X Y Z g f)
    (@comp_fapp0
      B
      (@fapp0 A B F X)
      (@fapp0 A B F Y)
      (@fapp0 A B F Z)
      (@fapp1_fapp0 A B F Y Z g)
      (@fapp1_fapp0 A B F X Y f))
    (@path_pseudo_laxity_postcomp_comp_path
      B B (@id_func B)
      (@fapp0 A B F X)
      (@fapp0 A B F Y)
      (@fapp0 A B F Z)
      (@fapp1_fapp0 A B F Y Z g)
      (@fapp1_fapp0 A B F X Y f));

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
≔ @eq_trans
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@strict_functor_compositor_lhs A B F X Y Z g f)
    (@readable_pseudo_post_stable_action A B F X Y Z g f)
    (@readable_pseudo_post_raw_source A B F X Y Z g f)
    (@readable_pseudo_post_formal_source_path A B F X Y Z g f)
    (@eq_trans
      (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
      (@readable_pseudo_post_stable_action A B F X Y Z g f)
      (@readable_pseudo_post_raw_target A B F X Y Z g f)
      (@readable_pseudo_post_raw_source A B F X Y Z g f)
      (@readable_pseudo_post_stable_comp_path A B F X Y Z g f)
      (@eq_trans
        (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
        (@readable_pseudo_post_raw_target A B F X Y Z g f)
        (@comp_fapp0
          B
          (@fapp0 A B F X)
          (@fapp0 A B F Y)
          (@fapp0 A B F Z)
          (@fapp1_fapp0 A B F Y Z g)
          (@fapp1_fapp0 A B F X Y f))
        (@readable_pseudo_post_raw_source A B F X Y Z g f)
        (@readable_pseudo_post_comp_raw_path A B F X Y Z g f)
        (@readable_pseudo_post_raw_owner_path A B F X Y Z g f)));

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
≔ @eq_trans
    (Hom B (@fapp0 A B F X) (@fapp0 A B F Z))
    (@strict_functor_compositor_rhs A B F X Y Z g f)
    (@readable_pseudo_post_stable_action A B F X Y Z g f)
    (@readable_pseudo_post_raw_target A B F X Y Z g f)
    (@readable_pseudo_post_formal_target_path A B F X Y Z g f)
    (@readable_pseudo_post_stable_comp_path A B F X Y Z g f);

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

// Explicit profile constructor. The sole mathematical field is native
// fixed-arrow omega-equivalence of the one readable cell derived from the
// intrinsic compositor.
injective symbol readable_pseudo_profile_intro
  [A B : Cat]
  [F : τ (Functor A B)]
  (evidence :
    Π X : τ (Obj A),
    Π Y : τ (Obj A),
    Π Z : τ (Obj A),
    Π g : τ (Hom A Y Z),
    Π f : τ (Hom A X Y),
      τ (@OmegaEquivAlong
        (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
        _ _
        (@readable_pseudo_post_cell A B F X Y Z g f)))
  : τ (@ReadablePseudoFunctorProfile A B F);

// Post/left readable compositor:
//   F[g] o F[f] ~= F[g o f]
// at the stable hom_postcomp owner used by source-varying hom families.
injective symbol readable_pseudo_post_evidence
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@ReadablePseudoFunctorProfile A B F))
  [X Y Z : τ (Obj A)]
  (g : τ (Hom A Y Z))
  (f : τ (Hom A X Y))
  : τ (@OmegaEquivAlong
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      _ _
      (@readable_pseudo_post_cell A B F X Y Z g f));

rule @readable_pseudo_post_evidence
      $A $B $F
      (@readable_pseudo_profile_intro $A $B $F $evidence)
      $X $Y $Z $g $f
  ↪ $evidence $X $Y $Z $g $f;

// Pre/right reverse adjustment uses the selected left inverse of the one
// fixed-forward post cell, followed by the existing post/pre endpoint reframe.
// The `OmegaEquivAlong` right inverse and both cancellation laws remain
// available to later coherence consumers.
symbol readable_pseudo_pre_inverse
  [A B : Cat]
  [F : τ (Functor A B)]
  (P : τ (@ReadablePseudoFunctorProfile A B F))
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
      (@readable_pseudo_post_evidence A B F P X Y Z g f));

// Supplied identity instance. Constructing this through `profile_intro`
// requires an extracted unit/normality interface, which remains separate.
constant symbol readable_pseudo_identity_profile
  (A : Cat)
  : τ (@ReadablePseudoFunctorProfile A A (@id_func A));

// Supplied composition instance. A transparent constructor requires the next
// internal action comparing the composite functor's intrinsic compositor with
// the two component profiles.
constant symbol readable_pseudo_comp_profile
  [A B C : Cat]
  [F : τ (Functor A B)]
  (PF : τ (@ReadablePseudoFunctorProfile A B F))
  [G : τ (Functor B C)]
  (PG : τ (@ReadablePseudoFunctorProfile B C G))
  : τ (@ReadablePseudoFunctorProfile
      A C (@comp_cat_fapp0 A B C G F));
