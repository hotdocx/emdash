/*
  Emdash v3.2: readable pseudofunctor profiles over ambient functor carriers.

  The active generic functor/transfor calculus exposes normal-lax compositor
  cells at formal internal-action endpoints. Consumers such as intrinsic
  cubical arrows require an invertible readable view of the existing
  compositor; its inverse supplies the opposite boundary direction.

  ReadablePseudoFunctorProfile is an abstract coherent capability indexed by
  its already-existing Functor carrier. It does not supply another compositor:
  fixed-forward `IsoCellEvidence` gives an inverse and cancellation paths for
  the existing post cell extracted from internal action. Higher coherence
  remains the next internal action. This adds no rewrite or proof-time unifier.

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

// Invertibility evidence for one already-selected arrow. The forward cell is
// an input, never an independently supplied profile field.
symbol IsoCellEvidence
  [C : Cat]
  [x y : τ (Obj C)]
  (cell : τ (Hom C x y))
  : Grpd
≔ `Σ_ inverse : τ (Hom C y x),
   `Σ_ _ : τ (
      @comp_fapp0 C x y x inverse cell
        =
      @id C x),
      @comp_fapp0 C y x y cell inverse
        =
      @id C y;

symbol iso_cell_inverse
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (evidence : τ (@IsoCellEvidence C x y cell))
  : τ (Hom C y x)
≔ sigma_Fst evidence;

symbol iso_cell_left
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (evidence : τ (@IsoCellEvidence C x y cell))
  : τ (
      @comp_fapp0 C x y x
        (@iso_cell_inverse C x y cell evidence) cell
        =
      @id C x)
≔ sigma_Fst (sigma_Snd evidence);

symbol iso_cell_right
  [C : Cat]
  [x y : τ (Obj C)]
  [cell : τ (Hom C x y)]
  (evidence : τ (@IsoCellEvidence C x y cell))
  : τ (
      @comp_fapp0 C y x y
        cell (@iso_cell_inverse C x y cell evidence)
        =
      @id C y)
≔ sigma_Snd (sigma_Snd evidence);

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

// Explicit profile constructor. The sole mathematical field is invertibility
// of the one readable cell derived from the intrinsic compositor.
injective symbol readable_pseudo_profile_intro
  [A B : Cat]
  [F : τ (Functor A B)]
  (evidence :
    Π X : τ (Obj A),
    Π Y : τ (Obj A),
    Π Z : τ (Obj A),
    Π g : τ (Hom A Y Z),
    Π f : τ (Hom A X Y),
      τ (@IsoCellEvidence
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
  : τ (@IsoCellEvidence
      (Hom_cat B (@fapp0 A B F X) (@fapp0 A B F Z))
      _ _
      (@readable_pseudo_post_cell A B F X Y Z g f));

rule @readable_pseudo_post_evidence
      $A $B $F
      (@readable_pseudo_profile_intro $A $B $F $evidence)
      $X $Y $Z $g $f
  ↪ $evidence $X $Y $Z $g $f;

// Pre/right inverse is derived from the inverse of the one fixed-forward post
// cell, followed by the existing post/pre endpoint reframe.
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
    (@iso_cell_inverse
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
