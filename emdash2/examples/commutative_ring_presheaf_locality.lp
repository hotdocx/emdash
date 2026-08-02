/*
  Reviewer for topology-visible invertibility support and the internal
  localization-factor cone over the category of elements of D(s).

  The closed zero-ring example checks that the selected universal factor
  reduces to the actual restriction map.  The reviewer also checks the
  internal cone's literal component and its derived objectwise coherence under
  a further restriction.  The cone is not yet claimed to be limiting; no
  descent equivalence, sheafhood, generated topology, Spec, or scheme is
  claimed.
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

// The two Sigma projections recover the literal domain object V in Op(K).
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U V : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    (Op_cat K)
    (@comm_ring_psh_invertibility_domain_func K O U s)
    (Struct_sigma (Struct_sigma V f) member)
  ≡ V;

// The induced value diagram computes at the same triple to O(V).
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U V : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    CommRing_cat
    (@comm_ring_psh_invertibility_value_diagram K O U s)
    (Struct_sigma (Struct_sigma V f) member)
  ≡ @comm_ring_psh_value K O V;

// One Transf owner carries the whole factor family and internal naturality.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s)) ⊢
  @comm_ring_psh_localization_factor_cone K O U s localization
  : τ (@Transf
      (@CommRingPshInvertibilityElements_cat K O U s)
      CommRing_cat
      (@Const_func
        (@CommRingPshInvertibilityElements_cat K O U s)
        CommRing_cat
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization))
      (@comm_ring_psh_invertibility_value_diagram K O U s));

// A literal cone component is exactly the already selected universal factor.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  [U V : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @tapp0_fapp0
    (@CommRingPshInvertibilityElements_cat K O U s)
    CommRing_cat
    (@Const_func
      (@CommRingPshInvertibilityElements_cat K O U s)
      CommRing_cat
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))
    (@comm_ring_psh_invertibility_value_diagram K O U s)
    (Struct_sigma (Struct_sigma V f) member)
    (@comm_ring_psh_localization_factor_cone K O U s localization)
  ≡ @comm_ring_psh_localization_factor_map_at_member
      K O U s localization V f member;

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

symbol zero_psh_invertibility_element
  : τ (Obj
      (@CommRingPshInvertibilityElements_cat
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj tt))
≔ @comm_ring_psh_invertibility_element
    Terminal_cat
    (@zero_comm_ring_psh Terminal_cat)
    Terminal_obj tt
    Terminal_obj
    (@id Terminal_cat Terminal_obj)
    (@zero_comm_ring_psh_invertible_along
      Terminal_cat Terminal_obj Terminal_obj
      (@id Terminal_cat Terminal_obj));

// The internal cone component reaches the same executable restriction map.
assert ⊢
  @tapp0_fapp0
    (@CommRingPshInvertibilityElements_cat
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt)
    CommRing_cat
    (@Const_func
      (@CommRingPshInvertibilityElements_cat
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj tt)
      CommRing_cat
      (@comm_ring_localization_target
        zero_comm_ring tt zero_localization_at_point))
    (@comm_ring_psh_invertibility_value_diagram
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt)
    zero_psh_invertibility_element
    (@comm_ring_psh_localization_factor_cone
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point)
  ≡ @comm_ring_psh_restriction_hom
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj Terminal_obj Terminal_obj;

// The direct factor at f o g equals restriction after the factor at f.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [W V : τ (Obj K)]
  (f : τ (Hom K V U))
  (g : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f))) ⊢
  @comm_ring_psh_localization_factor_restriction_path
    K O U s localization W V f g member
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O W))
      (@comm_ring_psh_localization_factor_map_at_member
        K O U s localization W (@comp_fapp0 K W V U f g)
        (@comm_ring_psh_invertible_along_restrict
          K O W V U f g s member))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)
        (@comm_ring_psh_value K O V)
        (@comm_ring_psh_value K O W)
        (@comm_ring_psh_restriction_hom K O W V g)
        (@comm_ring_psh_localization_factor_map_at_member
          K O U s localization V f member)));

// The competing factor package exposes the literal pointwise composite map.
assert ⊢
  @comm_ring_localization_factor_map
    zero_comm_ring zero_comm_ring zero_comm_ring
    zero_localization_map
    (@comm_ring_psh_restriction_hom
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj Terminal_obj
      (@comp_fapp0 Terminal_cat
        Terminal_obj Terminal_obj Terminal_obj Terminal_obj Terminal_obj))
    (@comm_ring_psh_localization_factor_after_restriction
      Terminal_cat
      (@zero_comm_ring_psh Terminal_cat)
      Terminal_obj tt
      zero_localization_at_point
      Terminal_obj Terminal_obj Terminal_obj Terminal_obj
      (@zero_comm_ring_psh_invertible_along
        Terminal_cat Terminal_obj Terminal_obj Terminal_obj))
  ≡ @comm_ring_hom_comp_pointwise
      zero_comm_ring zero_comm_ring zero_comm_ring
      (@comm_ring_psh_restriction_hom
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj Terminal_obj Terminal_obj)
      (@comm_ring_psh_localization_factor_map_at_member
        Terminal_cat
        (@zero_comm_ring_psh Terminal_cat)
        Terminal_obj tt
        zero_localization_at_point
        Terminal_obj Terminal_obj
        (@zero_comm_ring_psh_invertible_along
          Terminal_cat Terminal_obj Terminal_obj Terminal_obj));
