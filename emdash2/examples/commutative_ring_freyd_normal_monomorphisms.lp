/* Reviewer-facing witnessed formal Freyd normal-monomorphism consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_normal_monomorphisms;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @CommRingFreydMonomorphismWitness R W P Q f
  : Grpd;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  ⊢ @comm_ring_freyd_normal_mono_block_path R P Q T f tau a
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
      (@comm_ring_presentation_morphism_map R T Q tau));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  ⊢ @comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a
  : τ (@CommRingPresentationMorphism R T P);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  ⊢ @comm_ring_freyd_normal_mono_lift_law R W P Q T f m tau a
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_freyd_normal_mono_expected_relation_witness
          R W P Q T f m tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)
        (@comm_ring_presentation_matrix R T)));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  ⊢ @comm_ring_freyd_normal_mono_reconstruction_path
      R W P Q T f m tau a
  : τ (@= (@CommRingFreydHomSet R T Q)
      (@comm_ring_freyd_comp R T P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_normal_mono_lift R W P Q T f m tau a))
      (@comm_ring_freyd_hom_class R T Q tau));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  ⊢ @comm_ring_freyd_normal_mono_uniqueness_path
      R W P Q T f m tau a k reconstructs
  : τ (@= (@CommRingFreydHomSet R T P)
      (@comm_ring_freyd_hom_class R T P k)
      (@comm_ring_freyd_normal_mono_lift R W P Q T f m tau a));
