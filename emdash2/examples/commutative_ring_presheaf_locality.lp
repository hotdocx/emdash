/*
  Reviewer for topology-visible invertibility support and the pointwise
  localization factor selected at an actual member of D(s).

  The closed zero-ring example checks that the selected universal factor
  reduces to the actual restriction map.  No natural cone, descent limit,
  sheafhood, generated topology, Spec, or scheme is claimed here.
*/

require open emdash.emdash3_2_commutative_algebra_locality;
require open emdash.examples.commutative_ring_localization;
require open emdash.examples.commutative_ring_presheaf_invertibility;

// Coverhood is the transparent topology observation of the existing D(s).
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @CommRingPshInvertibilityCover K T O U s
  ≡ @groth_topology_covers
      K T U (@comm_ring_psh_invertibility_sieve K O U s);

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_invertibility_cover_is_prop K T O U s
  : τ (IsPropGrpd (@CommRingPshInvertibilityCover K T O U s));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U)) ⊢
  @chaotic_comm_ring_psh_invertibility_cover K O U s
  ≡ tt;

// An actual support member supplies a factor from the chosen localization.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_factor_at_member
    K O U s localization V f member
  : τ (@CommRingPshLocalizationFactorAlong
      K O U s localization V f);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_factor_map_at_member
    K O U s localization V f member
  : τ (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V));

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@CommRingPshSection K O U)) ⊢
  @comm_ring_psh_localization_factor_triangle_at
    K O U s localization V f member x
  : τ (@= (@CommRingPshSection K O V)
      (@comm_ring_hom_apply
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)
        (@comm_ring_hom_apply
          (@comm_ring_psh_value K O U)
          (@comm_ring_localization_target
            (@comm_ring_psh_value K O U) s localization)
          (@comm_ring_localization_map
            (@comm_ring_psh_value K O U) s localization)
          x))
      (@comm_ring_psh_restrict K O V U f x));

// Closed executable model: the selected zero-ring localization factor reduces
// to the actual restriction homomorphism of the constant presheaf.
symbol zero_psh_localization_factor_at_terminal_member
  : τ (@CommRingPshLocalizationFactorAlong
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point
      Terminal_obj Terminal_obj)
≔ @comm_ring_psh_localization_factor_at_member
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt
    zero_localization_at_point
    Terminal_obj Terminal_obj
    (@zero_comm_ring_psh_invertible_along
      Terminal_cat Terminal_obj Terminal_obj Terminal_obj);

assert ⊢ zero_psh_localization_factor_at_terminal_member
  : τ (@CommRingPshLocalizationFactorAlong
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point
      Terminal_obj Terminal_obj);

assert ⊢
  @comm_ring_psh_localization_factor_map_at_member
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt
    zero_localization_at_point
    Terminal_obj Terminal_obj
    (@zero_comm_ring_psh_invertible_along
      Terminal_cat Terminal_obj Terminal_obj Terminal_obj)
  ≡ @comm_ring_psh_restriction_hom
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj Terminal_obj Terminal_obj;
