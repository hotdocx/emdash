/*
  Capability-indexed witnessed Abelian structure for the formal Freyd category.

  This package combines the witnessed pre-Abelian construction with Posur
  Construction 3.14/3.15. Its normality families quantify over raw
  presentation morphisms carrying explicit monicity/epicity and test
  agreements. Reconstruction and raw-competitor uniqueness are therefore
  available constructively without decoding arbitrary paths in truncated
  quotient Homs.

  This is deliberately not a closed ComputationalAbelianCategory value. It
  adds no rewrite or unification rule.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_normal_epimorphisms;

symbol CommRingFreydWitnessedNormalMonoUniversal
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R) (λ T : τ _,
    @Pi_grpd (@CommRingPresentationMorphism R T Q) (λ tau : τ _,
      @Pi_grpd (@CommRingFreydNormalMonoTestAgreement R P Q T f tau)
        (λ a : τ _,
          @Product_grpd
            (@= (@CommRingFreydHomSet R T Q)
              (@comm_ring_freyd_comp R T P Q
                (@comm_ring_freyd_hom_class R P Q f)
                (@comm_ring_freyd_normal_mono_lift
                  R W P Q T f m tau a))
              (@comm_ring_freyd_hom_class R T Q tau))
            (@Pi_grpd (@CommRingPresentationMorphism R T P) (λ k : τ _,
              @Pi_grpd
                (@CommRingPresentationMorphismAgreement R T Q
                  (@comm_ring_presentation_morphism_map R T Q
                    (@comm_ring_presentation_morphism_comp R T P Q f k))
                  (@comm_ring_presentation_morphism_map R T Q tau))
                (λ reconstructs : τ _,
                  @= (@CommRingFreydHomSet R T P)
                    (@comm_ring_freyd_hom_class R T P k)
                    (@comm_ring_freyd_normal_mono_lift
                      R W P Q T f m tau a)))))));

symbol comm_ring_freyd_witnessed_normal_mono_universal
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  : τ (@CommRingFreydWitnessedNormalMonoUniversal R W P Q f m)
≔ λ T : τ (@CommRingPresentation R),
   λ tau : τ (@CommRingPresentationMorphism R T Q),
   λ a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau),
   @Product_pair_grpd _ _
      (@comm_ring_freyd_normal_mono_reconstruction_path
        R W P Q T f m tau a)
      (λ k : τ (@CommRingPresentationMorphism R T P),
        λ reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
          (@comm_ring_presentation_morphism_map R T Q
            (@comm_ring_presentation_morphism_comp R T P Q f k))
          (@comm_ring_presentation_morphism_map R T Q tau)),
        @comm_ring_freyd_normal_mono_uniqueness_path
          R W P Q T f m tau a k reconstructs);

symbol HasCommRingFreydWitnessedNormalMonomorphisms
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R) (λ P : τ _,
    @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
      @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
        @Pi_grpd (@CommRingFreydMonomorphismWitness R W P Q f) (λ m : τ _,
          @CommRingFreydWitnessedNormalMonoUniversal R W P Q f m))));

symbol comm_ring_freyd_has_witnessed_normal_monomorphisms
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : τ (@HasCommRingFreydWitnessedNormalMonomorphisms R W)
≔ λ P : τ (@CommRingPresentation R),
   λ Q : τ (@CommRingPresentation R),
   λ f : τ (@CommRingPresentationMorphism R P Q),
   λ m : τ (@CommRingFreydMonomorphismWitness R W P Q f),
   @comm_ring_freyd_witnessed_normal_mono_universal R W P Q f m;

symbol CommRingFreydWitnessedNormalEpiUniversal
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R) (λ T : τ _,
    @Pi_grpd (@CommRingPresentationMorphism R P T) (λ tau : τ _,
      @Pi_grpd (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau)
        (λ a : τ _,
          @Product_grpd
            (@= (@CommRingFreydHomSet R P T)
              (@comm_ring_freyd_comp R P Q T
                (@comm_ring_freyd_normal_epi_colift
                  R W P Q T f e tau a)
                (@comm_ring_freyd_hom_class R P Q f))
              (@comm_ring_freyd_hom_class R P T tau))
            (@Pi_grpd (@CommRingPresentationMorphism R Q T) (λ k : τ _,
              @Pi_grpd
                (@CommRingPresentationMorphismAgreement R P T
                  (@comm_ring_presentation_morphism_map R P T
                    (@comm_ring_presentation_morphism_comp R P Q T k f))
                  (@comm_ring_presentation_morphism_map R P T tau))
                (λ reconstructs : τ _,
                  @= (@CommRingFreydHomSet R Q T)
                    (@comm_ring_freyd_hom_class R Q T k)
                    (@comm_ring_freyd_normal_epi_colift
                      R W P Q T f e tau a)))))));

symbol comm_ring_freyd_witnessed_normal_epi_universal
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingFreydWitnessedNormalEpiUniversal R W P Q f e)
≔ λ T : τ (@CommRingPresentation R),
   λ tau : τ (@CommRingPresentationMorphism R P T),
   λ a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau),
   @Product_pair_grpd _ _
      (@comm_ring_freyd_normal_epi_reconstruction_path
        R W P Q T f e tau a)
      (λ k : τ (@CommRingPresentationMorphism R Q T),
        λ reconstructs : τ (@CommRingPresentationMorphismAgreement R P T
          (@comm_ring_presentation_morphism_map R P T
            (@comm_ring_presentation_morphism_comp R P Q T k f))
          (@comm_ring_presentation_morphism_map R P T tau)),
        @comm_ring_freyd_normal_epi_uniqueness_path
          R W P Q T f e tau a k reconstructs);

symbol HasCommRingFreydWitnessedNormalEpimorphisms
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R) (λ P : τ _,
    @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
      @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
        @Pi_grpd (@CommRingFreydEpimorphismWitness R P Q f) (λ e : τ _,
          @CommRingFreydWitnessedNormalEpiUniversal R W P Q f e))));

symbol comm_ring_freyd_has_witnessed_normal_epimorphisms
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : τ (@HasCommRingFreydWitnessedNormalEpimorphisms R W)
≔ λ P : τ (@CommRingPresentation R),
   λ Q : τ (@CommRingPresentation R),
   λ f : τ (@CommRingPresentationMorphism R P Q),
   λ e : τ (@CommRingFreydEpimorphismWitness R P Q f),
   @comm_ring_freyd_witnessed_normal_epi_universal R W P Q f e;

symbol CommRingFreydWitnessedAbelian
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : Grpd
≔ `Σ_ A : τ (@CommRingFreydWitnessedPreAbelian R W),
   @Product_grpd
      (@HasCommRingFreydWitnessedNormalMonomorphisms R W)
      (@HasCommRingFreydWitnessedNormalEpimorphisms R W);

symbol comm_ring_freyd_witnessed_abelian
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : τ (@CommRingFreydWitnessedAbelian R W)
≔ @Struct_sigma
    (@CommRingFreydWitnessedPreAbelian R W)
    (λ _ : τ _,
      @Product_grpd
        (@HasCommRingFreydWitnessedNormalMonomorphisms R W)
        (@HasCommRingFreydWitnessedNormalEpimorphisms R W))
    (@comm_ring_freyd_witnessed_preabelian R W)
    (@Product_pair_grpd _ _
      (@comm_ring_freyd_has_witnessed_normal_monomorphisms R W)
      (@comm_ring_freyd_has_witnessed_normal_epimorphisms R W));

symbol comm_ring_freyd_witnessed_abelian_preabelian
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  (A : τ (@CommRingFreydWitnessedAbelian R W))
  : τ (@CommRingFreydWitnessedPreAbelian R W)
≔ sigma_Fst A;

symbol comm_ring_freyd_witnessed_abelian_mono_lifts
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  (A : τ (@CommRingFreydWitnessedAbelian R W))
  : τ (@HasCommRingFreydWitnessedNormalMonomorphisms R W)
≔ sigma_Fst (sigma_Snd A);

symbol comm_ring_freyd_witnessed_abelian_epi_colifts
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  (A : τ (@CommRingFreydWitnessedAbelian R W))
  : τ (@HasCommRingFreydWitnessedNormalEpimorphisms R W)
≔ sigma_Snd (sigma_Snd A);
