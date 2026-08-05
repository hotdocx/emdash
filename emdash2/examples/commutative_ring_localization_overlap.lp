/*
  Reviewer-facing PSSS-08c0F example: the universal-property comparison
  R[1/(f*g)] -> R[1/f][1/g] is a whole internal commutative-ring
  omega-equivalence.
*/

require open emdash.emdash3_2_commutative_algebra_localization_overlap;

// Contractibility gives equality of the selected maps in any two factors.
assert (R L S : τ CommRing)
  (localization_map : τ (@CommRingHom R L))
  (h : τ (@CommRingHom R S))
  (contractible : τ (IsContr (@CommRingLocalizationFactor
      R L S localization_map h)))
  (factor0 factor1 : τ (@CommRingLocalizationFactor
      R L S localization_map h)) ⊢
  @comm_ring_localization_factor_maps_equal
    R L S localization_map h contractible factor0 factor1
  : τ (@= (@CommRingHom L S)
      (@comm_ring_localization_factor_map
        R L S localization_map h factor0)
      (@comm_ring_localization_factor_map
        R L S localization_map h factor1));

// The staged reverse map is a whole left inverse of the forward comparison.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_left_law
    R f g iterated product_localization comparison
  : τ (@=
      (@CommRingHom
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization))
      (@comm_ring_hom_comp
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)));

// Two successive localization-uniqueness steps give the whole right inverse.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_right_law
    R f g iterated product_localization comparison
  : τ (@=
      (@CommRingHom
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_target R f g iterated))
      (@comm_ring_hom_comp
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_localization_target
          R (@comm_ring_mul R f g) product_localization)
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_comparison_forward_map
          R f g iterated product_localization comparison)
        (@comm_ring_iterated_localization_comparison_reverse_map
          R f g iterated product_localization comparison))
      (@comm_ring_hom_id
        (@comm_ring_iterated_localization_target R f g iterated)));

// Fixed-forward evidence is the semantic overlap owner.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_omega_equiv_along
    R f g iterated product_localization comparison
  : τ (@OmegaEquivAlong
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison));

// A first-class OmegaEquiv facade is derived from that fixed-arrow evidence.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_omega_equiv
    R f g iterated product_localization comparison
  : τ (@OmegaEquiv
      CommRing_cat
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated));

// Both inverse slots compute to the same canonical staged reverse map.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_along_left_inv
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization comparison;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_along_right_inv
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_reverse_map
      R f g iterated product_localization comparison;

// The facade retains the canonical forward map and fixed-arrow evidence.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_to
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_omega_equiv
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_evidence
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_omega_equiv
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison;

// The evidence projections expose the named whole cancellation paths.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_along_left_law
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_left_law
      R f g iterated product_localization comparison;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @omega_equiv_along_right_law
    CommRing_cat
    (@comm_ring_localization_target
      R (@comm_ring_mul R f g) product_localization)
    (@comm_ring_iterated_localization_target R f g iterated)
    (@comm_ring_iterated_localization_comparison_forward_map
      R f g iterated product_localization comparison)
    (@comm_ring_iterated_localization_comparison_omega_equiv_along
      R f g iterated product_localization comparison)
  ≡ @comm_ring_iterated_localization_comparison_right_law
      R f g iterated product_localization comparison;
