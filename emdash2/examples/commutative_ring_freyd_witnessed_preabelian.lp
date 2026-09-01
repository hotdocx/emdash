/* Reviewer-facing capability consumers for witnessed Freyd pre-Abelian data. */

require open emdash.emdash3_2_commutative_algebra_freyd_witnessed_preabelian;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  ⊢ @comm_ring_freyd_witnessed_preabelian_additive R W
      (@comm_ring_freyd_witnessed_preabelian R W)
  ≡ @comm_ring_freyd_additive R;

// The whole kernel capability projects the canonical quotient annihilation.
assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ sigma_Fst
      ((@comm_ring_freyd_witnessed_preabelian_kernels R W
        (@comm_ring_freyd_witnessed_preabelian R W)) P Q f)
  ≡ @comm_ring_freyd_kernel_annihilation_path R W P Q f;

// A retained zero agreement selects the canonical lift and reconstruction.
assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  ⊢ sigma_Fst
      ((sigma_Snd
        ((@comm_ring_freyd_witnessed_preabelian_kernels R W
          (@comm_ring_freyd_witnessed_preabelian R W)) P Q f)) T tau a)
  ≡ @comm_ring_freyd_kernel_reconstruction_path R W P Q T f tau a;

// An explicitly reconstructing raw competitor is quotient-equal to that lift.
assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  (k : τ (@CommRingPresentationMorphism R T
    (@comm_ring_freyd_kernel_presentation R W P Q f)))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T P
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_presentation_morphism_comp R T
        (@comm_ring_freyd_kernel_presentation R W P Q f) P
        (@comm_ring_freyd_kernel_embedding_raw R W P Q f) k))
    (@comm_ring_presentation_morphism_map R T P tau)))
  ⊢ (sigma_Snd
      ((sigma_Snd
        ((@comm_ring_freyd_witnessed_preabelian_kernels R W
          (@comm_ring_freyd_witnessed_preabelian R W)) P Q f)) T tau a))
      k reconstructs
  ≡ @comm_ring_freyd_kernel_uniqueness_path
      R W P Q T f tau a k reconstructs;

// The cokernel capability has the exact dual witness-enriched observations.
assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  ⊢ sigma_Fst
      ((@comm_ring_freyd_witnessed_preabelian_cokernels R W
        (@comm_ring_freyd_witnessed_preabelian R W)) P Q f)
  ≡ @comm_ring_freyd_cokernel_annihilation_path R P Q f;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  ⊢ sigma_Fst
      ((sigma_Snd
        ((@comm_ring_freyd_witnessed_preabelian_cokernels R W
          (@comm_ring_freyd_witnessed_preabelian R W)) P Q f)) T h a)
  ≡ @comm_ring_freyd_cokernel_reconstruction_path R P Q T f h a;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P Q T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  (k : τ (@CommRingPresentationMorphism R
    (@comm_ring_freyd_cokernel_presentation R P Q f) T))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R Q T
    (@comm_ring_presentation_morphism_map R Q T
      (@comm_ring_presentation_morphism_comp R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f) T
        k (@comm_ring_freyd_cokernel_projection_raw R P Q f)))
    (@comm_ring_presentation_morphism_map R Q T h)))
  ⊢ (sigma_Snd
      ((sigma_Snd
        ((@comm_ring_freyd_witnessed_preabelian_cokernels R W
          (@comm_ring_freyd_witnessed_preabelian R W)) P Q f)) T h a))
      k reconstructs
  ≡ @comm_ring_freyd_cokernel_uniqueness_path
      R P Q T f h a k reconstructs;
