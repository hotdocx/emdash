/*
  Reviewer-facing PSSS-06a example: complete set-carrier commutative-ring
  objects before ring morphisms, CommRing_cat, localization, or polynomials.
*/

require open emdash.emdash3_2_commutative_algebra;

// A carrier package exposes both its decoded classifier and retained sethood.
assert (R : τ CommRing) ⊢
  @comm_ring_carrier R
  : Grpd;

assert (R : τ CommRing) ⊢
  @comm_ring_carrier_is_set R
  : τ (IsSetGrpd (@comm_ring_carrier R));

// Operations are ordinary functions on the selected carrier.
assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_add R x y
  : τ (@comm_ring_carrier R);

assert (R : τ CommRing)
  (x : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_neg R x
  : τ (@comm_ring_carrier R);

assert (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R)) ⊢
  @comm_ring_mul R x y
  : τ (@comm_ring_carrier R);

// The retained law package has readable projections.
assert (R : τ CommRing) ⊢
  @comm_ring_add_assoc_law R
  : τ (@CommRingAddAssoc
      (@comm_ring_carrier R)
      (@comm_ring_ops R));

assert (R : τ CommRing) ⊢
  @comm_ring_left_distrib_law R
  : τ (@CommRingLeftDistrib
      (@comm_ring_carrier R)
      (@comm_ring_ops R));

// Concrete one-element zero ring; zero and one need not be distinct.
assert ⊢ @comm_ring_carrier zero_comm_ring ≡ Unit_grpd;

assert ⊢ @comm_ring_zero zero_comm_ring ≡ tt;

assert ⊢ @comm_ring_one zero_comm_ring ≡ tt;

assert ⊢
  @comm_ring_zero zero_comm_ring
  ≡ @comm_ring_one zero_comm_ring;

assert ⊢ @comm_ring_add zero_comm_ring tt tt ≡ tt;

assert ⊢ @comm_ring_neg zero_comm_ring tt ≡ tt;

assert ⊢ @comm_ring_mul zero_comm_ring tt tt ≡ tt;

// The open Unit laws use its contraction path and reduce at the constructor.
assert ⊢
  (@comm_ring_add_zero_law zero_comm_ring) tt
  ≡ @eq_refl Unit_grpd tt;

assert ⊢
  (@comm_ring_mul_one_law zero_comm_ring) tt
  ≡ @eq_refl Unit_grpd tt;

// No broad package eta or ring-category structure is introduced here.
assertnot (R : τ CommRing) ⊢
  R
  ≡ @comm_ring_intro
      (@comm_ring_carrier_package R)
      (@comm_ring_structure R);
