/*
  Reviewer-facing PSSS-07b example: universal-property comparison between
  localization at f*g and localization first at f, then at the image of g.
*/

require open emdash.emdash3_2_commutative_algebra_localization_comparison;

// The selected structured composition computes only through its carrier view.
assert (R S T : τ CommRing)
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R T
    (@comm_ring_hom_comp_pointwise R S T g f) x
  ≡ @comm_ring_hom_apply S T g
      (@comm_ring_hom_apply R S f x);

// Typed reflexivity exercises the proof-time comparison to generic comp.
assert (R S T : τ CommRing)
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S)) ⊢
  @comm_ring_hom_comp_pointwise_path R S T g f
  : τ (@= (@CommRingHom R T)
      (@comm_ring_hom_comp R S T g f)
      (@comm_ring_hom_comp_pointwise R S T g f));

// Whole generic composition still has no carrier-application runtime beta.
assertnot (R S T : τ CommRing)
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R T (@comm_ring_hom_comp R S T g f) x
  ≡ @comm_ring_hom_apply S T g
      (@comm_ring_hom_apply R S f x);

// Unit evidence is stable under ring maps and finite multiplication.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R x)) ⊢
  @comm_ring_hom_preserves_unit R S h x u
  : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h x));

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R x))
  (v : τ (@CommRingUnitEvidence R y)) ⊢
  @comm_ring_unit_mul R x y u v
  : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y));

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y))) ⊢
  @comm_ring_unit_mul_left R x y u
  : τ (@CommRingUnitEvidence R x);

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  (u : τ (@CommRingUnitEvidence R (@comm_ring_mul R x y))) ⊢
  @comm_ring_unit_mul_right R x y u
  : τ (@CommRingUnitEvidence R y);

// The two-stage package retains both chosen localization stages.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R)) ⊢
  @CommRingIteratedLocalizationAt R f g
  : Grpd;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g)) ⊢
  @comm_ring_iterated_localization_first R f g iterated
  : τ (@CommRingLocalizationAt R f);

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g)) ⊢
  @comm_ring_iterated_localization_map R f g iterated
  : τ (@CommRingHom R
      (@comm_ring_iterated_localization_target R f g iterated));

// Its structure map sends f*g to a unit by the two stage unit laws.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g)) ⊢
  @comm_ring_iterated_localization_inverts_product R f g iterated
  : τ (@CommRingUnitEvidence
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_hom_apply
        R
        (@comm_ring_iterated_localization_target R f g iterated)
        (@comm_ring_iterated_localization_map R f g iterated)
        (@comm_ring_mul R f g)));

// A chosen localization at f*g yields canonical comparison data both ways.
assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_iterated_localization_comparison
    R f g iterated product_localization
  : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization);

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_iterated_localization_comparison_forward_factor
    R f g iterated product_localization
    (@comm_ring_iterated_localization_comparison
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_forward_factor
      R f g iterated product_localization;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g))) ⊢
  @comm_ring_iterated_localization_comparison_reverse_factor
    R f g iterated product_localization
    (@comm_ring_iterated_localization_comparison
      R f g iterated product_localization)
  ≡ @comm_ring_iterated_localization_reverse_factor
      R f g iterated product_localization;

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_forward_map
    R f g iterated product_localization comparison
  : τ (@CommRingHom
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated));

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_reverse_map
    R f g iterated product_localization comparison
  : τ (@CommRingHom
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization));

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_forward_agreement
    R f g iterated product_localization comparison
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_comparison_forward_map
        R f g iterated product_localization comparison)
      (@comm_ring_iterated_localization_map R f g iterated));

assert (R : τ CommRing)
  (f g : τ (@comm_ring_carrier R))
  (iterated : τ (@CommRingIteratedLocalizationAt R f g))
  (product_localization : τ (@CommRingLocalizationAt
      R (@comm_ring_mul R f g)))
  (comparison : τ (@CommRingIteratedLocalizationComparison
      R f g iterated product_localization)) ⊢
  @comm_ring_iterated_localization_comparison_reverse_agreement
    R f g iterated product_localization comparison
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_iterated_localization_target R f g iterated)
      (@comm_ring_localization_target
        R (@comm_ring_mul R f g) product_localization)
      (@comm_ring_iterated_localization_map R f g iterated)
      (@comm_ring_iterated_localization_comparison_reverse_map
        R f g iterated product_localization comparison)
      (@comm_ring_localization_map
        R (@comm_ring_mul R f g) product_localization));
