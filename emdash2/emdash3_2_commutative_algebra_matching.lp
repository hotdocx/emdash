/*
  Computational matching families from localization elements.

  For the semantic support D(s), pull the Path-valued carrier family back to
  the category of elements of D(s).  Its Pi category consists of coherent
  families of elements of O(V) indexed by literal support members
  (V,f,member).  A chosen element of O(U)[1/s] restricts through every selected
  localization factor and therefore determines one such matching family.

  The matching-family classifier carries restriction coherence internally.
  PathLift then makes the construction functorial on equality paths between
  localization elements.  The sole local computation rule exposes a literal
  component through the existing full fibre-covariance action; generic Pi,
  Catd, and path-action owners retain all naturality and arrow action.

  This module constructs only the localization-to-matching direction.  It
  does not supply a glue/inverse map, prove a descent or sheaf equivalence,
  claim that the localization-factor cone is limiting, or construct a
  generated topology, Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra_locality;

/*
  Carrier family over support elements.

  At a literal element (V,f,member), the fibre is Path_cat(|O(V)|).  Its arrow
  action is inherited by pulling back the selected full-action CommRing
  carrier family along the internally functorial value diagram.
*/
symbol comm_ring_psh_localization_matching_catd
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  : τ (Catd (@CommRingPshInvertibilityElements_cat K O U s))
≔ @Pullback_catd
    (@CommRingPshInvertibilityElements_cat K O U s)
    CommRing_cat
    comm_ring_carrier_catd
    (@comm_ring_psh_invertibility_value_diagram K O U s);

// Transparent category of coherent carrier-valued families over D(s).
symbol CommRingPshLocalizationMatching_cat
  [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s : τ (@CommRingPshSection K O U))
  : Cat
≔ @Pi_cat
    (@CommRingPshInvertibilityElements_cat K O U s)
    (@comm_ring_psh_localization_matching_catd K O U s);

/*
  Stable coherent section selected by x in the localization target.

  The typed Pi object owns all compatibility under arrows of the support-
  elements category.  The literal component beta below only exposes the
  already selected factor-map application.
*/
injective symbol comm_ring_psh_localization_matching_section
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  (x : τ (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization)))
  : τ (Obj (@CommRingPshLocalizationMatching_cat K O U s));

/*
  Literal matching component.

  All four structural tapp0 slots remain inferred: the nested Sigma object
  and matching-section head recover the base, families, endpoints, and result
  fibre.  Supplying x to fib_cov_tapp0_func before the selected structured map
  preserves the full-action carrier computation chosen by its owner.
*/
rule @tapp0_fapp0
      _
      _
      _
      _
      (Struct_sigma (Struct_sigma $V $f) $member)
      (@comm_ring_psh_localization_matching_section
        $K $O $U $s $localization $x)
  ↪ @Obj_func
      (Path_cat (@comm_ring_carrier (@comm_ring_psh_value $K $O $V)))
      (@fapp0
        (Path_cat (@CommRingHom
          (@comm_ring_localization_target
            (@comm_ring_psh_value $K $O $U) $s $localization)
          (@comm_ring_psh_value $K $O $V)))
        (Path_cat (@comm_ring_carrier (@comm_ring_psh_value $K $O $V)))
        (@fib_cov_tapp0_func
          CommRing_cat
          comm_ring_carrier_catd
          (@comm_ring_localization_target
            (@comm_ring_psh_value $K $O $U) $s $localization)
          (@comm_ring_psh_value $K $O $V)
          $x)
        (@comm_ring_psh_localization_factor_map_at_member
          $K $O $U $s $localization $V $f $member));

/*
  Restriction from localization elements to coherent matching families.

  PathLift supplies both object action and equality-path action from the one
  section-valued function; no external naturality or path-coherence field is
  added.
*/
symbol comm_ring_psh_localization_matching_restriction_func
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s : τ (@CommRingPshSection K O U))
  (localization : τ (@CommRingLocalizationAt
      (@comm_ring_psh_value K O U) s))
  : τ (Functor
      (Path_cat (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)))
      (@CommRingPshLocalizationMatching_cat K O U s))
≔ @path_lift_fapp0
    (@comm_ring_carrier
      (@comm_ring_localization_target
        (@comm_ring_psh_value K O U) s localization))
    (@CommRingPshLocalizationMatching_cat K O U s)
    (λ x : τ (@comm_ring_carrier
        (@comm_ring_localization_target
          (@comm_ring_psh_value K O U) s localization)),
      @comm_ring_psh_localization_matching_section
        K O U s localization x);
