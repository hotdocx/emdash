/*
  Reviewer for identity localization at an already invertible element.

  The model is parametric in an arbitrary commutative ring.  In particular,
  localization at one is constructed without assuming a localization package
  or a fraction representation.
*/

require open emdash.emdash3_2_commutative_algebra_localization_unit;

// One is canonically a unit with itself as selected inverse.
assert (R : τ CommRing) ⊢
  @comm_ring_one_unit R
  : τ (@CommRingUnitEvidence R (@comm_ring_one R));

assert (R : τ CommRing) ⊢
  @comm_ring_unit_inverse
    R (@comm_ring_one R) (@comm_ring_one_unit R)
  ≡ @comm_ring_one R;

assert (R : τ CommRing) ⊢
  @comm_ring_unit_law
    R (@comm_ring_one R) (@comm_ring_one_unit R)
  ≡ (@comm_ring_mul_one_law R) (@comm_ring_one R);

// The selected factor through the identity has the original map as projection.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_localization_factor_map
    R R S (@comm_ring_hom_id_pointwise R) h
    (@comm_ring_unit_localization_factor_center R S h)
  ≡ h;

// Its full structured factorization space is constructively contractible.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S)) ⊢
  @comm_ring_unit_localization_factor_is_contr R S h
  : τ (IsContr (@CommRingLocalizationFactor
      R R S (@comm_ring_hom_id_pointwise R) h));

// Any supplied unit makes the pointwise identity a localization at that element.
assert (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f)) ⊢
  @comm_ring_unit_is_identity_localization R f unit
  : τ (@IsCommRingLocalizationAt
      R f R (@comm_ring_hom_id_pointwise R));

assert (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f)) ⊢
  @comm_ring_unit_identity_localization R f unit
  : τ (@CommRingLocalizationAt R f);

// The selected target and localization map retain their computational form.
assert (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f)) ⊢
  @comm_ring_localization_target
    R f (@comm_ring_unit_identity_localization R f unit)
  ≡ R;

assert (R : τ CommRing)
  (f : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f)) ⊢
  @comm_ring_localization_map
    R f (@comm_ring_unit_identity_localization R f unit)
  ≡ @comm_ring_hom_id_pointwise R;

assert (R : τ CommRing)
  (f x : τ (@comm_ring_carrier R))
  (unit : τ (@CommRingUnitEvidence R f)) ⊢
  @comm_ring_hom_apply
    R R
    (@comm_ring_localization_map
      R f (@comm_ring_unit_identity_localization R f unit))
    x
  ≡ x;

// In particular, every ring has a selected, computing localization at one.
assert (R : τ CommRing) ⊢
  @comm_ring_identity_localization_at_one R
  : τ (@CommRingLocalizationAt R (@comm_ring_one R));

assert (R : τ CommRing) ⊢
  @comm_ring_localization_target
    R (@comm_ring_one R) (@comm_ring_identity_localization_at_one R)
  ≡ R;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply
    R R
    (@comm_ring_localization_map
      R (@comm_ring_one R) (@comm_ring_identity_localization_at_one R))
    x
  ≡ x;
