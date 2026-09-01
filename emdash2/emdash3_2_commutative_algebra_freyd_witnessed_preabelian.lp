/*
  Capability-parameterized witnessed Freyd pre-Abelian structure.

  The package combines the existing additive Freyd category with the
  canonical kernel and cokernel constructions. Its universal quantifiers range
  over raw presentation morphisms carrying the explicit agreements needed by
  the constructive quotient. It therefore exposes annihilation,
  reconstruction, and uniqueness for every witnessed test without postulating
  a decoder from arbitrary set-truncated paths back to agreement witnesses.

  This is deliberately not the stronger closed quotient-level
  PreAbelianCategory package. It adds no rewrite or unification rule.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_kernels;

// The selected kernel has quotient annihilation and is universal for every
// raw test supplied with the agreements needed to construct and compare lifts.
symbol CommRingFreydWitnessedKernelUniversal
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : Grpd
≔ @Product_grpd
    (@= (@CommRingFreydHomSet R
        (@comm_ring_freyd_kernel_presentation R W P Q f) Q)
      (@comm_ring_freyd_comp R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_kernel_embedding R W P Q f))
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_kernel_presentation R W P Q f) Q))
    (@Pi_grpd (@CommRingPresentation R) (λ T : τ _,
      @Pi_grpd (@CommRingPresentationMorphism R T P) (λ tau : τ _,
        @Pi_grpd
          (@CommRingPresentationMorphismAgreement R T Q
            (@comm_ring_presentation_morphism_map R T Q
              (@comm_ring_presentation_morphism_comp R T P Q f tau))
            (@comm_ring_presentation_morphism_map R T Q
              (@comm_ring_presentation_morphism_zero R T Q)))
          (λ a : τ _,
            @Product_grpd
              (@= (@CommRingFreydHomSet R T P)
                (@comm_ring_freyd_comp R T
                  (@comm_ring_freyd_kernel_presentation R W P Q f) P
                  (@comm_ring_freyd_kernel_embedding R W P Q f)
                  (@comm_ring_freyd_kernel_lift R W P Q T f tau a))
                (@comm_ring_freyd_hom_class R T P tau))
              (@Pi_grpd
                (@CommRingPresentationMorphism R T
                  (@comm_ring_freyd_kernel_presentation R W P Q f))
                (λ k : τ _,
                  @Pi_grpd
                    (@CommRingPresentationMorphismAgreement R T P
                      (@comm_ring_presentation_morphism_map R T P
                        (@comm_ring_presentation_morphism_comp R T
                          (@comm_ring_freyd_kernel_presentation R W P Q f) P
                          (@comm_ring_freyd_kernel_embedding_raw R W P Q f) k))
                      (@comm_ring_presentation_morphism_map R T P tau))
                    (λ _ : τ _,
                      @= (@CommRingFreydHomSet R T
                          (@comm_ring_freyd_kernel_presentation R W P Q f))
                        (@comm_ring_freyd_hom_class R T
                          (@comm_ring_freyd_kernel_presentation R W P Q f) k)
                        (@comm_ring_freyd_kernel_lift R W P Q T f tau a))))))));

symbol comm_ring_freyd_witnessed_kernel_universal
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydWitnessedKernelUniversal R W P Q f)
≔ @Product_pair_grpd _ _
    (@comm_ring_freyd_kernel_annihilation_path R W P Q f)
    (λ T : τ (@CommRingPresentation R),
      λ tau : τ (@CommRingPresentationMorphism R T P),
      λ a : τ (@CommRingPresentationMorphismAgreement R T Q
        (@comm_ring_presentation_morphism_map R T Q
          (@comm_ring_presentation_morphism_comp R T P Q f tau))
        (@comm_ring_presentation_morphism_map R T Q
          (@comm_ring_presentation_morphism_zero R T Q))),
      @Product_pair_grpd _ _
        (@comm_ring_freyd_kernel_reconstruction_path
          R W P Q T f tau a)
        (λ k : τ (@CommRingPresentationMorphism R T
            (@comm_ring_freyd_kernel_presentation R W P Q f)),
          λ reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
            (@comm_ring_presentation_morphism_map R T P
              (@comm_ring_presentation_morphism_comp R T
                (@comm_ring_freyd_kernel_presentation R W P Q f) P
                (@comm_ring_freyd_kernel_embedding_raw R W P Q f) k))
            (@comm_ring_presentation_morphism_map R T P tau)),
          @comm_ring_freyd_kernel_uniqueness_path
            R W P Q T f tau a k reconstructs));

// Dually, the selected cokernel is universal for raw tests carrying the
// explicit zero-composite and reconstruction agreements.
symbol CommRingFreydWitnessedCokernelUniversal
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : Grpd
≔ @Product_grpd
    (@= (@CommRingFreydHomSet R P
        (@comm_ring_freyd_cokernel_presentation R P Q f))
      (@comm_ring_freyd_comp R P Q
        (@comm_ring_freyd_cokernel_presentation R P Q f)
        (@comm_ring_freyd_cokernel_projection R P Q f)
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_freyd_cokernel_presentation R P Q f)))
    (@Pi_grpd (@CommRingPresentation R) (λ T : τ _,
      @Pi_grpd (@CommRingPresentationMorphism R Q T) (λ h : τ _,
        @Pi_grpd
          (@CommRingPresentationMorphismAgreement R P T
            (@comm_ring_presentation_morphism_map R P T
              (@comm_ring_presentation_morphism_comp R P Q T h f))
            (@comm_ring_presentation_morphism_map R P T
              (@comm_ring_presentation_morphism_zero R P T)))
          (λ a : τ _,
            @Product_grpd
              (@= (@CommRingFreydHomSet R Q T)
                (@comm_ring_freyd_comp R Q
                  (@comm_ring_freyd_cokernel_presentation R P Q f) T
                  (@comm_ring_freyd_cokernel_colift R P Q T f h a)
                  (@comm_ring_freyd_cokernel_projection R P Q f))
                (@comm_ring_freyd_hom_class R Q T h))
              (@Pi_grpd
                (@CommRingPresentationMorphism R
                  (@comm_ring_freyd_cokernel_presentation R P Q f) T)
                (λ k : τ _,
                  @Pi_grpd
                    (@CommRingPresentationMorphismAgreement R Q T
                      (@comm_ring_presentation_morphism_map R Q T
                        (@comm_ring_presentation_morphism_comp R Q
                          (@comm_ring_freyd_cokernel_presentation R P Q f) T
                          k (@comm_ring_freyd_cokernel_projection_raw R P Q f)))
                      (@comm_ring_presentation_morphism_map R Q T h))
                    (λ _ : τ _,
                      @= (@CommRingFreydHomSet R
                          (@comm_ring_freyd_cokernel_presentation R P Q f) T)
                        (@comm_ring_freyd_hom_class R
                          (@comm_ring_freyd_cokernel_presentation R P Q f) T k)
                        (@comm_ring_freyd_cokernel_colift R P Q T f h a))))))));

symbol comm_ring_freyd_witnessed_cokernel_universal
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydWitnessedCokernelUniversal R P Q f)
≔ @Product_pair_grpd _ _
    (@comm_ring_freyd_cokernel_annihilation_path R P Q f)
    (λ T : τ (@CommRingPresentation R),
      λ h : τ (@CommRingPresentationMorphism R Q T),
      λ a : τ (@CommRingPresentationMorphismAgreement R P T
        (@comm_ring_presentation_morphism_map R P T
          (@comm_ring_presentation_morphism_comp R P Q T h f))
        (@comm_ring_presentation_morphism_map R P T
          (@comm_ring_presentation_morphism_zero R P T))),
      @Product_pair_grpd _ _
        (@comm_ring_freyd_cokernel_reconstruction_path R P Q T f h a)
        (λ k : τ (@CommRingPresentationMorphism R
            (@comm_ring_freyd_cokernel_presentation R P Q f) T),
          λ reconstructs : τ (@CommRingPresentationMorphismAgreement R Q T
            (@comm_ring_presentation_morphism_map R Q T
              (@comm_ring_presentation_morphism_comp R Q
                (@comm_ring_freyd_cokernel_presentation R P Q f) T
                k (@comm_ring_freyd_cokernel_projection_raw R P Q f)))
            (@comm_ring_presentation_morphism_map R Q T h)),
          @comm_ring_freyd_cokernel_uniqueness_path
            R P Q T f h a k reconstructs));

symbol HasCommRingFreydWitnessedKernels
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R) (λ P : τ _,
    @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
      @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
        @CommRingFreydWitnessedKernelUniversal R W P Q f)));

symbol comm_ring_freyd_has_witnessed_kernels
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : τ (@HasCommRingFreydWitnessedKernels R W)
≔ λ P : τ (@CommRingPresentation R),
   λ Q : τ (@CommRingPresentation R),
   λ f : τ (@CommRingPresentationMorphism R P Q),
   @comm_ring_freyd_witnessed_kernel_universal R W P Q f;

symbol HasCommRingFreydWitnessedCokernels
  (R : τ CommRing)
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R) (λ P : τ _,
    @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
      @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
        @CommRingFreydWitnessedCokernelUniversal R P Q f)));

symbol comm_ring_freyd_has_witnessed_cokernels
  (R : τ CommRing)
  : τ (@HasCommRingFreydWitnessedCokernels R)
≔ λ P : τ (@CommRingPresentation R),
   λ Q : τ (@CommRingPresentation R),
   λ f : τ (@CommRingPresentationMorphism R P Q),
   @comm_ring_freyd_witnessed_cokernel_universal R P Q f;

// This is deliberately witness-enriched, not the stronger closed quotient
// PreAbelianCategory package, whose construction needs effective path decoding.
symbol CommRingFreydWitnessedPreAbelian
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : Grpd
≔ `Σ_ A : τ (@AdditiveCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R)),
   @Product_grpd
      (@HasCommRingFreydWitnessedKernels R W)
      (@HasCommRingFreydWitnessedCokernels R);

symbol comm_ring_freyd_witnessed_preabelian
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  : τ (@CommRingFreydWitnessedPreAbelian R W)
≔ @Struct_sigma
    (@AdditiveCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R))
    (λ _ : τ _,
      @Product_grpd
        (@HasCommRingFreydWitnessedKernels R W)
        (@HasCommRingFreydWitnessedCokernels R))
    (@comm_ring_freyd_additive R)
    (@Product_pair_grpd _ _
      (@comm_ring_freyd_has_witnessed_kernels R W)
      (@comm_ring_freyd_has_witnessed_cokernels R));

symbol comm_ring_freyd_witnessed_preabelian_additive
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  (A : τ (@CommRingFreydWitnessedPreAbelian R W))
  : τ (@AdditiveCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R))
≔ sigma_Fst A;

symbol comm_ring_freyd_witnessed_preabelian_kernels
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  (A : τ (@CommRingFreydWitnessedPreAbelian R W))
  : τ (@HasCommRingFreydWitnessedKernels R W)
≔ sigma_Fst (sigma_Snd A);

symbol comm_ring_freyd_witnessed_preabelian_cokernels
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  (A : τ (@CommRingFreydWitnessedPreAbelian R W))
  : τ (@HasCommRingFreydWitnessedCokernels R)
≔ sigma_Snd (sigma_Snd A);
