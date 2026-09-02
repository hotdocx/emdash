/* Reviewer-facing witnessed formal Freyd normal-epimorphism consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_normal_epimorphisms;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ @CommRingFreydEpimorphismWitness R P Q f
  : Grpd;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  ⊢ @comm_ring_freyd_epimorphism_block_path R P Q f e
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R Q))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_epimorphism_target_component R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R Q)));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  ⊢ @comm_ring_freyd_normal_epi_relation_factor R W P Q f e
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R Q));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  (tau : τ (@CommRingPresentationMorphism R P T))
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  ⊢ @comm_ring_freyd_normal_epi_colift_law R W P Q T f e tau a
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_freyd_normal_epi_expected_relation_witness
          R W P Q T f e tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_freyd_normal_epi_colift_map R P Q T f e tau)
        (@comm_ring_presentation_matrix R Q)));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  (tau : τ (@CommRingPresentationMorphism R P T))
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  ⊢ @comm_ring_freyd_normal_epi_colift_raw R W P Q T f e tau a
  : τ (@CommRingPresentationMorphism R Q T);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  (tau : τ (@CommRingPresentationMorphism R P T))
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  ⊢ @comm_ring_freyd_normal_epi_reconstruction_path
      R W P Q T f e tau a
  : τ (@= (@CommRingFreydHomSet R P T)
      (@comm_ring_freyd_comp R P Q T
        (@comm_ring_freyd_normal_epi_colift R W P Q T f e tau a)
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_hom_class R P T tau));
