/*
  Reviewer for the universal-property localization R[1/0] = 0.

  This is a parametric, non-identity-shaped but degenerate localization.  The
  checks exercise the derived zero algebra, structured maps to and from the
  zero ring, full factor contractibility, and target/map computation.
*/

require open emdash.emdash3_2_commutative_algebra_localization_zero;

// The retained ring axioms derive the expected elementary zero laws.
assert (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R a a) a)) ⊢
  @comm_ring_add_idempotent_is_zero R a idempotent
  : τ (@= (@comm_ring_carrier R) a (@comm_ring_zero R));

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_mul_zero_right R x
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x (@comm_ring_zero R))
      (@comm_ring_zero R));

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_mul_zero_left R x
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_zero R) x)
      (@comm_ring_zero R));

assert (R : τ CommRing) ⊢
  @comm_ring_neg_zero R
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_neg R (@comm_ring_zero R)));

// Invertible zero collapses the carrier, constructively.
assert (R : τ CommRing)
  (unit : τ (@CommRingUnitEvidence R (@comm_ring_zero R))) ⊢
  @comm_ring_zero_unit_zero_one R unit
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_one R));

assert (R : τ CommRing)
  (zero_one : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_one R)))
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_zero_one_contracts R zero_one x
  : τ (@= (@comm_ring_carrier R) (@comm_ring_zero R) x);

// The selected structure map is the unique point map into the zero ring.
assert (R : τ CommRing) ⊢
  @comm_ring_hom_to_zero R
  : τ (@CommRingHom R zero_comm_ring);

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply R zero_comm_ring (@comm_ring_hom_to_zero R) x
  ≡ tt;

// Conversely zero=one supplies the unique structured map out of the zero ring.
assert (S : τ CommRing)
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S))) ⊢
  @comm_ring_hom_from_zero S zero_one
  : τ (@CommRingHom zero_comm_ring S);

assert (S : τ CommRing)
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S)))
  (x : τ Unit_grpd) ⊢
  @comm_ring_hom_apply
    zero_comm_ring S (@comm_ring_hom_from_zero S zero_one) x
  ≡ @comm_ring_zero S;

// Every admissible map has a constructively contractible factorization.
assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (zero_one : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S))) ⊢
  @comm_ring_zero_localization_factor_is_contr R S h zero_one
  : τ (IsContr (@CommRingLocalizationFactor
      R zero_comm_ring S (@comm_ring_hom_to_zero R) h));

assert (R S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h (@comm_ring_zero R)))) ⊢
  @comm_ring_hom_inverting_zero_zero_one R S h unit
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_zero S)
      (@comm_ring_one S));

// The universal property and selected package retain their full types.
assert (R : τ CommRing) ⊢
  @comm_ring_zero_is_zero_localization R
  : τ (@IsCommRingLocalizationAt
      R (@comm_ring_zero R) zero_comm_ring (@comm_ring_hom_to_zero R));

assert (R : τ CommRing) ⊢
  @comm_ring_zero_localization R
  : τ (@CommRingLocalizationAt R (@comm_ring_zero R));

// Target and carrier action compute without a fraction representation.
assert (R : τ CommRing) ⊢
  @comm_ring_localization_target
    R (@comm_ring_zero R) (@comm_ring_zero_localization R)
  ≡ zero_comm_ring;

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_hom_apply
    R zero_comm_ring
    (@comm_ring_localization_map
      R (@comm_ring_zero R) (@comm_ring_zero_localization R))
    x
  ≡ tt;
