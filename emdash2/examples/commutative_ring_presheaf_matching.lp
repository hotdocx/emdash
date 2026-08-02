/*
  Reviewer for computational localization-to-matching restriction.

  A localization element determines a coherent Pi section over the category
  of elements of D(s).  Its literal component is application of the selected
  localization factor.  PathLift supplies a genuine functor on localization
  elements and equality paths, so no external naturality or coherence field
  is requested from the consumer.

  The closed zero-ring model reaches the actual presheaf restriction.  This
  reviewer does not claim an inverse/glue map, descent equivalence, sheafhood,
  a limiting cone, generated topology, Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra_matching;
require open emdash.examples.commutative_ring_presheaf_locality;

// The matching carrier over a literal support member is Path_cat(|O(V)|).
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @Fibre_cat
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ Path_cat (@comm_ring_carrier (@comm_ring_psh_value K O V));

// A literal section component computes by the selected universal factor map.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))) ⊢
  @piapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s)
    (@comm_ring_psh_localization_matching_section
      K O U s localization x)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ @comm_ring_hom_apply
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization V f member)
      x;

// PathLift exposes the matching section as the restriction functor's object action.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))) ⊢
  @fapp0
    (Path_cat (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
    (@CommRingPshLocalizationMatching_cat K O U s)
    (@comm_ring_psh_localization_matching_restriction_func
      K O U s localization)
    x
  ≡ @comm_ring_psh_localization_matching_section
      K O U s localization x;

// End to end, functor application followed by Pi evaluation still computes.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [V U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))) ⊢
  @piapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s)
    (@fapp0
      (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)))
      (@CommRingPshLocalizationMatching_cat K O U s)
      (@comm_ring_psh_localization_matching_restriction_func
        K O U s localization)
      x)
    (@comm_ring_psh_invertibility_element K O U s V f member)
  ≡ @comm_ring_hom_apply
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization V f member)
      x;

// Equality paths between localization elements map internally to arrows
// between the corresponding coherent matching sections.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (x y : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
  (p : τ (@=
      (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization))
      x y)) ⊢
  @fapp1_fapp0
    (Path_cat (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
    (@CommRingPshLocalizationMatching_cat K O U s)
    (@comm_ring_psh_localization_matching_restriction_func
      K O U s localization)
    x y p
  : τ (Hom
      (@CommRingPshLocalizationMatching_cat K O U s)
      (@comm_ring_psh_localization_matching_section
        K O U s localization x)
      (@comm_ring_psh_localization_matching_section
        K O U s localization y));

// Closed executable model: the zero-localization section evaluates to the
// actual restriction of tt at the literal terminal support member.
assert ⊢
  @piapp0
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
      zero_localization_at_point
      tt)
    (@comm_ring_psh_invertibility_element
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      Terminal_obj
      (@id Terminal_cat Terminal_obj)
      (@zero_comm_ring_psh_invertible_along
        Terminal_cat Terminal_obj Terminal_obj
        (@id Terminal_cat Terminal_obj)))
  ≡ @comm_ring_psh_restrict
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj Terminal_obj
      (@id Terminal_cat Terminal_obj)
      tt;

// The closed restriction functor computes first to the coherent section.
assert ⊢
  @fapp0
    (Path_cat (@comm_ring_carrier zero_comm_ring))
    (@CommRingPshLocalizationMatching_cat
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt)
    (@comm_ring_psh_localization_matching_restriction_func
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point)
    tt
  ≡ @comm_ring_psh_localization_matching_section
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point
      tt;

// The complete closed route through the restriction functor also evaluates to
// the actual constant-presheaf restriction.
assert ⊢
  @piapp0
    (@CommRingPshInvertibilityElements_cat
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt)
    (@comm_ring_psh_localization_matching_catd
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt)
    (@fapp0
      (Path_cat (@comm_ring_carrier zero_comm_ring))
      (@CommRingPshLocalizationMatching_cat
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj tt)
      (@comm_ring_psh_localization_matching_restriction_func
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj tt
        zero_localization_at_point)
      tt)
    (@comm_ring_psh_invertibility_element
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      Terminal_obj
      (@id Terminal_cat Terminal_obj)
      (@zero_comm_ring_psh_invertible_along
        Terminal_cat Terminal_obj Terminal_obj
        (@id Terminal_cat Terminal_obj)))
  ≡ @comm_ring_psh_restrict
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj Terminal_obj
      (@id Terminal_cat Terminal_obj)
      tt;
