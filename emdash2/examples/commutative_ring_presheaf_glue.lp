/*
  Reviewer for selected computational localization glue.

  The generic checks exercise the selected functor, its internal arrow action,
  both inverse observations, and the literal Cartier component equation. They
  then assume the stronger fixed-forward locality witness and inspect both
  whole composite-functor paths and its derived compatibility package. The
  zero-ring model derives actual component-view glue data: its glue functor is
  constant at tt, and Unit contractibility supplies both observed laws without
  a rewrite rule. It does not claim the stronger whole locality witness.

  This is locality over D(s), which need not cover U.  The reviewer does not
  claim ordinary sheaf descent, a categorical DefIso, generated topology,
  Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra_glue;
require open emdash.examples.commutative_ring_presheaf_matching;

// Constructor projection preserves the selected functor literally.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue_func : τ (@CommRingPshLocalizationGlueFunctor
      K O U s localization))
  (glue_restrict : τ (@CommRingPshLocalizationGlueRestrictLaw
      K O U s localization glue_func))
  (restrict_glue : τ
      (@CommRingPshLocalizationRestrictGlueComponentLaw
        K O U s localization glue_func)) ⊢
  @comm_ring_psh_localization_glue_func
    K O U s localization
    (@comm_ring_psh_localization_glue_intro
      K O U s localization glue_func glue_restrict restrict_glue)
  ≡ glue_func;

// Glue carries full matching-arrow action through the ordinary functor owner.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (m n : τ (Obj (@CommRingPshLocalizationMatching_cat K O U s)))
  (eta : τ (Hom (@CommRingPshLocalizationMatching_cat K O U s) m n)) ⊢
  @fapp1_fapp0
    (@CommRingPshLocalizationMatching_cat K O U s)
    (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
    (@comm_ring_psh_localization_glue_func K O U s localization glue)
    m n eta
  : τ (Hom
      (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
      (@comm_ring_psh_localization_glue
        K O U s localization glue m)
      (@comm_ring_psh_localization_glue
        K O U s localization glue n));

// The selected left-inverse law is exposed on every localization element.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (x : τ (@CommRingPshLocalizationCarrier K O U s localization)) ⊢
  @comm_ring_psh_localization_glue_restrict_path
    K O U s localization glue x
  : τ (@=
      (@CommRingPshLocalizationCarrier K O U s localization)
      (@comm_ring_psh_localization_glue
        K O U s localization glue
        (@comm_ring_psh_localization_matching_section
          K O U s localization x))
      x);

// At a literal support member, the right law is the Cartier factor equation.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (glue : τ (@CommRingPshLocalizationGlue K O U s localization))
  (matching : τ (Obj
      (@CommRingPshLocalizationMatching_cat K O U s)))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_glue_at_member_path
    K O V U s localization glue matching f member
  : τ (@=
      (@comm_ring_carrier (@comm_ring_psh_value K O V))
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)
        (@comm_ring_psh_localization_glue
          K O U s localization glue matching))
      (@piapp0
        (@CommRingPshInvertibilityElements_cat K O U s)
        (@comm_ring_psh_localization_matching_catd K O U s)
        matching
        (@comm_ring_psh_invertibility_element K O U s V f member)));

// The stronger capability fixes the existing restriction as its forward functor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s)) ⊢
  @CommRingPshLocalizationLocality K O U s localization
  ≡ @OmegaEquivAlong
      Cat_cat
      (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
      (@CommRingPshLocalizationMatching_cat K O U s)
      (@comm_ring_psh_localization_matching_restriction_func
        K O U s localization);

// Glue after restriction is equality of whole endofunctors.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (locality : τ (@CommRingPshLocalizationLocality
      K O U s localization)) ⊢
  @comm_ring_psh_localization_locality_glue_restrict_functor_path
    K O U s localization locality
  : τ (@=
      (Obj (Functor_cat
        (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
        (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))))
      (@comp_cat_fapp0
        (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
        (@CommRingPshLocalizationMatching_cat K O U s)
        (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
        (@comm_ring_psh_localization_locality_glue_func
          K O U s localization locality)
        (@comm_ring_psh_localization_matching_restriction_func
          K O U s localization))
      (@id_func
        (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))));

// Restriction after the same selected glue is also equality of whole functors.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (locality : τ (@CommRingPshLocalizationLocality
      K O U s localization)) ⊢
  @comm_ring_psh_localization_locality_restrict_glue_functor_path
    K O U s localization locality
  : τ (@=
      (Obj (Functor_cat
        (@CommRingPshLocalizationMatching_cat K O U s)
        (@CommRingPshLocalizationMatching_cat K O U s)))
      (@comp_cat_fapp0
        (@CommRingPshLocalizationMatching_cat K O U s)
        (Path_cat (@CommRingPshLocalizationCarrier K O U s localization))
        (@CommRingPshLocalizationMatching_cat K O U s)
        (@comm_ring_psh_localization_matching_restriction_func
          K O U s localization)
        (@comm_ring_psh_localization_locality_glue_func
          K O U s localization locality))
      (@id_func (@CommRingPshLocalizationMatching_cat K O U s)));

// Whole locality derives the earlier component-view glue package.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (locality : τ (@CommRingPshLocalizationLocality
      K O U s localization)) ⊢
  @comm_ring_psh_localization_locality_legacy_glue
    K O U s localization locality
  : τ (@CommRingPshLocalizationGlue K O U s localization);

// --------------------------------------------------------------------------
// Derived nonempty zero-ring model.

symbol zero_glue_unit_path
  (x y : τ Unit_grpd)
  : τ (@= Unit_grpd x y)
≔ @eq_trans
    Unit_grpd x tt y
    (@eq_sym Unit_grpd tt x
      (@is_contr_path Unit_grpd unit_is_contr x))
    (@is_contr_path Unit_grpd unit_is_contr y);

symbol ZeroCommRingPshLocalizationMatching_cat
  : Cat
≔ @CommRingPshLocalizationMatching_cat
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt;

symbol zero_comm_ring_psh_localization_glue_func
  : τ (Functor
      ZeroCommRingPshLocalizationMatching_cat
      (Path_cat Unit_grpd))
≔ @Const_func
    ZeroCommRingPshLocalizationMatching_cat
    (Path_cat Unit_grpd)
    tt;

symbol zero_comm_ring_psh_localization_glue_restrict
  : τ (@CommRingPshLocalizationGlueRestrictLaw
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point
      zero_comm_ring_psh_localization_glue_func)
≔ λ x : τ Unit_grpd,
    @is_contr_path Unit_grpd unit_is_contr x;

symbol zero_comm_ring_psh_localization_restrict_glue_component
  : τ (@CommRingPshLocalizationRestrictGlueComponentLaw
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point
      zero_comm_ring_psh_localization_glue_func)
≔ λ matching : τ (Obj ZeroCommRingPshLocalizationMatching_cat),
    λ element : τ (Obj
        (@CommRingPshInvertibilityElements_cat
          Terminal_cat
          (@zero_comm_ring_psh Terminal_cat)
          Terminal_obj tt)),
      @zero_glue_unit_path
        (@piapp0
          (@CommRingPshInvertibilityElements_cat
            Terminal_cat
            (@zero_comm_ring_psh Terminal_cat)
            Terminal_obj tt)
          (@comm_ring_psh_localization_matching_catd
            Terminal_cat
            (@zero_comm_ring_psh Terminal_cat)
            Terminal_obj tt)
          (@comm_ring_psh_localization_matching_section
            Terminal_cat
            (@zero_comm_ring_psh Terminal_cat)
            Terminal_obj tt
            zero_localization_at_point tt)
          element)
        (@piapp0
          (@CommRingPshInvertibilityElements_cat
            Terminal_cat
            (@zero_comm_ring_psh Terminal_cat)
            Terminal_obj tt)
          (@comm_ring_psh_localization_matching_catd
            Terminal_cat
            (@zero_comm_ring_psh Terminal_cat)
            Terminal_obj tt)
          matching element);

symbol zero_comm_ring_psh_localization_glue
  : τ (@CommRingPshLocalizationGlue
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point)
≔ @comm_ring_psh_localization_glue_intro
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt
    zero_localization_at_point
    zero_comm_ring_psh_localization_glue_func
    zero_comm_ring_psh_localization_glue_restrict
    zero_comm_ring_psh_localization_restrict_glue_component;

assert ⊢ zero_comm_ring_psh_localization_glue
  : τ (@CommRingPshLocalizationGlue
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point);

// The concrete glue operation computes on every matching object.
assert (matching : τ (Obj ZeroCommRingPshLocalizationMatching_cat)) ⊢
  @comm_ring_psh_localization_glue
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt
    zero_localization_at_point
    zero_comm_ring_psh_localization_glue
    matching
  ≡ tt;

// In particular, glue after restriction computes to the original closed point.
assert ⊢
  @comm_ring_psh_localization_glue
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt
    zero_localization_at_point
    zero_comm_ring_psh_localization_glue
    (@comm_ring_psh_localization_matching_section
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point tt)
  ≡ tt;

// The closed Cartier path reaches the actual zero-presheaf restriction.
assert ⊢
  @comm_ring_psh_localization_glue_at_member_path
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj Terminal_obj tt
    zero_localization_at_point
    zero_comm_ring_psh_localization_glue
    (@comm_ring_psh_localization_matching_section
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point tt)
    (@id Terminal_cat Terminal_obj)
    (@zero_comm_ring_psh_invertible_along
      Terminal_cat Terminal_obj Terminal_obj
      (@id Terminal_cat Terminal_obj))
  : τ (@=
      Unit_grpd
      (@comm_ring_hom_apply
        zero_comm_ring zero_comm_ring
        (@comm_ring_psh_localization_factor_map_at_member
          Terminal_cat
          (@zero_comm_ring_psh Terminal_cat)
          Terminal_obj tt
          zero_localization_at_point
          Terminal_obj
          (@id Terminal_cat Terminal_obj)
          (@zero_comm_ring_psh_invertible_along
            Terminal_cat Terminal_obj Terminal_obj
            (@id Terminal_cat Terminal_obj)))
        tt)
      (@comm_ring_psh_restrict
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj Terminal_obj
        (@id Terminal_cat Terminal_obj)
        tt));
