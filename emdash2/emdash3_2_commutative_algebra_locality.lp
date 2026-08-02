/*
  Topology-visible invertibility support and pointwise localization factors.

  The semantic support D(s) of a section is already an ordinary sieve whose
  literal membership computes to unit evidence for the restricted section.
  This rule-free one-way module first exposes the proposition that D(s) covers
  in a supplied Grothendieck topology.  It then consumes an actual member
  f:V->U of D(s): the universal property of a chosen localization O(U)[1/s]
  selects a structured factor to O(V), together with its pointwise triangle
  over the presheaf restriction O(f).

  This is the pointwise computational front of the Cartier-style comparison
  lim_{V in D(s)} O(V) = O(U)[1/s].  It deliberately does not claim that the
  factors form a natural cone, that the cone is limiting, that O is a sheaf,
  or that a generated Zariski topology, Spec, or scheme has been constructed.
*/

require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_sites;

// A section is locally invertible when its semantic support sieve covers.
symbol CommRingPshInvertibilityCover
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  : Grpd
≔ @groth_topology_covers
    K T U (@comm_ring_psh_invertibility_sieve K O U s);

symbol comm_ring_psh_invertibility_cover_is_prop
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  : τ (IsPropGrpd (@CommRingPshInvertibilityCover K T O U s))
≔ @covers_is_prop
    K
    (@groth_topology_cover_predicate K T)
    U
    (@comm_ring_psh_invertibility_sieve K O U s);

// Closed topology model: every semantic invertibility support covers.
symbol chaotic_comm_ring_psh_invertibility_cover
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  : τ (@CommRingPshInvertibilityCover
      K (@chaotic_groth_topology K) O U s)
≔ tt;

/*
  Candidate factorization space from a chosen localization O(U)[1/s] to O(V)
  over the actual structured presheaf restriction O(f):O(U)->O(V).
*/
symbol CommRingPshLocalizationFactorAlong
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  : Grpd
≔ @CommRingLocalizationFactor
    (@comm_ring_psh_value K O U)
    (@comm_ring_localization_target
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_value K O V)
    (@comm_ring_localization_map
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_restriction_hom K O V U f);

// Membership f∈D(s) supplies the universal factor selected by localization.
symbol comm_ring_psh_localization_factor_at_member
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@CommRingPshLocalizationFactorAlong
      K O U s localization V f)
≔ @is_contr_center
    (@CommRingPshLocalizationFactorAlong K O U s localization V f)
    (@comm_ring_localization_factorization_is_contr
      (@comm_ring_psh_value K O U)
      s
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_localization_map
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_localization_property
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_psh_restriction_hom K O V U f)
      member);

symbol comm_ring_psh_localization_factor_map_at_member
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  : τ (@CommRingHom
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V))
≔ @comm_ring_localization_factor_map
    (@comm_ring_psh_value K O U)
    (@comm_ring_localization_target
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_value K O V)
    (@comm_ring_localization_map
      (@comm_ring_psh_value K O U) s localization)
    (@comm_ring_psh_restriction_hom K O V U f)
    (@comm_ring_psh_localization_factor_at_member
      K O U s localization V f member);

// The universal factor triangle is exposed directly on carrier elements.
symbol comm_ring_psh_localization_factor_triangle_at
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  [V : τ (Obj K)]
  (f : τ (Hom K V U))
  (member : τ (@SieveMembership
      K U
      (@comm_ring_psh_invertibility_sieve K O U s)
      (Struct_sigma V f)))
  (x : τ (@CommRingPshSection K O U))
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
      (@comm_ring_psh_restrict K O V U f x))
≔ (@comm_ring_localization_factor_agreement
      (@comm_ring_psh_value K O U)
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_value K O V)
      (@comm_ring_localization_map
        (@comm_ring_psh_value K O U) s localization)
      (@comm_ring_psh_restriction_hom K O V U f)
      (@comm_ring_psh_localization_factor_at_member
        K O U s localization V f member)) x;
