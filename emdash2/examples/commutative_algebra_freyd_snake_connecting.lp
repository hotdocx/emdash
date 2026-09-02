/* Reviewer-facing witnessed formal Freyd snake normal factors. */

require open emdash.emdash3_2_commutative_algebra_freyd_snake_connecting;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (F G U H : τ (@CommRingPresentation R))
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  ⊢ @comm_ring_freyd_snake_connecting_raw R W F G U H
      p1 p1_epic middle p1_test q2 q2_monic q2_test
  : τ (@CommRingPresentationMorphism R G H);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (F G U H : τ (@CommRingPresentation R))
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  ⊢ @comm_ring_freyd_snake_u_reconstruction_path R W F G U
      p1 p1_epic middle p1_test
  : τ (@= (@CommRingFreydHomSet R F U)
      (@comm_ring_freyd_comp R F G U
        (@comm_ring_freyd_snake_u R W F G U
          p1 p1_epic middle p1_test)
        (@comm_ring_freyd_hom_class R F G p1))
      (@comm_ring_freyd_hom_class R F U middle));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (F G U H : τ (@CommRingPresentation R))
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  ⊢ @comm_ring_freyd_witnessed_snake_connecting R W F G U H
      p1 p1_epic middle p1_test q2 q2_monic q2_test
  : τ (@CommRingFreydWitnessedSnakeConnecting R W F G U H
      p1 p1_epic middle p1_test q2 q2_monic q2_test);
