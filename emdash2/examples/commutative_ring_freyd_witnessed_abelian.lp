/* Reviewer-facing capability-indexed formal Freyd Abelian consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_witnessed_abelian;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  ⊢ @comm_ring_freyd_witnessed_abelian R W
  : τ (@CommRingFreydWitnessedAbelian R W);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (A : τ (@CommRingFreydWitnessedAbelian R W))
  ⊢ @comm_ring_freyd_witnessed_abelian_preabelian R W A
  : τ (@CommRingFreydWitnessedPreAbelian R W);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (A : τ (@CommRingFreydWitnessedAbelian R W))
  ⊢ @comm_ring_freyd_witnessed_abelian_mono_lifts R W A
  : τ (@HasCommRingFreydWitnessedNormalMonomorphisms R W);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (A : τ (@CommRingFreydWitnessedAbelian R W))
  ⊢ @comm_ring_freyd_witnessed_abelian_epi_colifts R W A
  : τ (@HasCommRingFreydWitnessedNormalEpimorphisms R W);
