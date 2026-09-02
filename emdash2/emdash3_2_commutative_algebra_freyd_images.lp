/*
  Witnessed formal image/coimage comparison in the Freyd category.

  Coimage is the selected cokernel of the selected kernel embedding; image is
  the selected kernel of the selected cokernel projection. The comparison is
  the existing kernel lift of the existing cokernel colift. Every displayed
  factorization is backed by raw presentation agreements and then promoted to
  the truncated Freyd Hom. No image primitive or runtime rule is introduced.

  Comparison invertibility is the downstream witnessed normality layer.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_witnessed_abelian;

symbol comm_ring_freyd_image_kernel_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_kernel_presentation R W P Q f;

symbol comm_ring_freyd_coimage_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_cokernel_presentation R
    (@comm_ring_freyd_image_kernel_presentation R W P Q f) P
    (@comm_ring_freyd_kernel_embedding_raw R W P Q f);

symbol comm_ring_freyd_image_cokernel_presentation
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_cokernel_presentation R P Q f;

symbol comm_ring_freyd_image_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_kernel_presentation R W Q
    (@comm_ring_freyd_image_cokernel_presentation R P Q f)
    (@comm_ring_freyd_cokernel_projection_raw R P Q f);

symbol comm_ring_freyd_coimage_projection_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R P
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_cokernel_projection_raw R
    (@comm_ring_freyd_image_kernel_presentation R W P Q f) P
    (@comm_ring_freyd_kernel_embedding_raw R W P Q f);

symbol comm_ring_freyd_coimage_projection
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R P
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_hom_class R P
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_coimage_projection_raw R W P Q f);

symbol comm_ring_freyd_image_embedding_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_image_presentation R W P Q f) Q)
≔ @comm_ring_freyd_kernel_embedding_raw R W Q
    (@comm_ring_freyd_image_cokernel_presentation R P Q f)
    (@comm_ring_freyd_cokernel_projection_raw R P Q f);

symbol comm_ring_freyd_image_embedding
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f) Q)
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_image_presentation R W P Q f) Q
    (@comm_ring_freyd_image_embedding_raw R W P Q f);

symbol comm_ring_freyd_coastriction_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_coimage_presentation R W P Q f) Q)
≔ @comm_ring_freyd_cokernel_colift_raw R
    (@comm_ring_freyd_image_kernel_presentation R W P Q f) P Q
    (@comm_ring_freyd_kernel_embedding_raw R W P Q f) f
    (@comm_ring_freyd_kernel_annihilation_agreement R W P Q f);

symbol comm_ring_freyd_coastriction
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_coimage_presentation R W P Q f) Q)
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_coimage_presentation R W P Q f) Q
    (@comm_ring_freyd_coastriction_raw R W P Q f);

symbol comm_ring_freyd_coastriction_annihilation_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_cokernel_presentation R P Q f)
        (@comm_ring_presentation_morphism_comp R
          (@comm_ring_freyd_coimage_presentation R W P Q f) Q
          (@comm_ring_freyd_image_cokernel_presentation R P Q f)
          (@comm_ring_freyd_cokernel_projection_raw R P Q f)
          (@comm_ring_freyd_coastriction_raw R W P Q f)))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_cokernel_presentation R P Q f)
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_cokernel_presentation R P Q f))))
≔ @comm_ring_freyd_cokernel_annihilation_agreement R P Q f;

symbol comm_ring_freyd_coimage_image_comparison_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f))
≔ @comm_ring_freyd_kernel_lift_raw R W Q
    (@comm_ring_freyd_image_cokernel_presentation R P Q f)
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_cokernel_projection_raw R P Q f)
    (@comm_ring_freyd_coastriction_raw R W P Q f)
    (@comm_ring_freyd_coastriction_annihilation_agreement R W P Q f);

symbol comm_ring_freyd_coimage_image_comparison
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f))
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f);

symbol comm_ring_freyd_image_factorization_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R P Q)
≔ @comm_ring_presentation_morphism_comp R P
    (@comm_ring_freyd_coimage_presentation R W P Q f) Q
    (@comm_ring_presentation_morphism_comp R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f) Q
      (@comm_ring_freyd_image_embedding_raw R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
    (@comm_ring_freyd_coimage_projection_raw R W P Q f);

symbol comm_ring_freyd_image_factorization_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q
        (@comm_ring_freyd_image_factorization_raw R W P Q f))
      (@comm_ring_presentation_morphism_map R P Q f))
≔ @comm_ring_presentation_agreement_trans R P Q
    (@comm_ring_presentation_morphism_map R P Q
      (@comm_ring_freyd_image_factorization_raw R W P Q f))
    (@comm_ring_presentation_morphism_map R P Q
      (@comm_ring_presentation_morphism_comp R P
        (@comm_ring_freyd_coimage_presentation R W P Q f) Q
        (@comm_ring_freyd_coastriction_raw R W P Q f)
        (@comm_ring_freyd_coimage_projection_raw R W P Q f)))
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_agreement_precomp R P
      (@comm_ring_freyd_coimage_presentation R W P Q f) Q
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_coimage_presentation R W P Q f) Q
        (@comm_ring_presentation_morphism_comp R
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f) Q
          (@comm_ring_freyd_image_embedding_raw R W P Q f)
          (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_coimage_presentation R W P Q f) Q
        (@comm_ring_freyd_coastriction_raw R W P Q f))
      (@comm_ring_freyd_kernel_reconstruction_agreement R W Q
        (@comm_ring_freyd_image_cokernel_presentation R P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_cokernel_projection_raw R P Q f)
        (@comm_ring_freyd_coastriction_raw R W P Q f)
        (@comm_ring_freyd_coastriction_annihilation_agreement R W P Q f))
      (@comm_ring_presentation_morphism_map R P
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_coimage_projection_raw R W P Q f)))
    (@comm_ring_freyd_cokernel_reconstruction_agreement R
      (@comm_ring_freyd_image_kernel_presentation R W P Q f) P Q
      (@comm_ring_freyd_kernel_embedding_raw R W P Q f) f
      (@comm_ring_freyd_kernel_annihilation_agreement R W P Q f));

symbol comm_ring_freyd_image_factorization_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_hom_class R P Q
        (@comm_ring_freyd_image_factorization_raw R W P Q f))
      (@comm_ring_freyd_hom_class R P Q f))
≔ @comm_ring_freyd_agreement_path R P Q
    (@comm_ring_freyd_image_factorization_raw R W P Q f) f
    (@comm_ring_freyd_image_factorization_agreement R W P Q f);

symbol comm_ring_freyd_comparison_kernel_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_kernel_presentation R W
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f);

symbol comm_ring_freyd_comparison_kernel_embedding_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_kernel_embedding_raw R W
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f);

symbol comm_ring_freyd_comparison_cokernel_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_cokernel_presentation R
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f);

symbol comm_ring_freyd_comparison_cokernel_projection_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f))
≔ @comm_ring_freyd_cokernel_projection_raw R
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f);

// Explicit comparison monicity and epicity are the checkable boundary used
// by the normality algorithms and by the proof-CAS adapter.
symbol CommRingFreydComparisonBimorphismWitness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : Grpd
≔ @Product_grpd
    (@CommRingFreydMonomorphismWitness R W
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
    (@CommRingFreydEpimorphismWitness R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f));

symbol comm_ring_freyd_comparison_monomorphism_witness
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingFreydMonomorphismWitness R W
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
≔ sigma_Fst b;

symbol comm_ring_freyd_comparison_epimorphism_witness
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingFreydEpimorphismWitness R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
≔ sigma_Snd b;

symbol comm_ring_freyd_comparison_mono_identity_test_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingFreydNormalMonoTestAgreement R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)
      (@comm_ring_presentation_morphism_identity R
        (@comm_ring_freyd_image_presentation R W P Q f)))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_cokernel_presentation R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
      (@comm_ring_presentation_morphism_comp R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
        (@comm_ring_freyd_comparison_cokernel_projection_raw R W P Q f)
        (@comm_ring_presentation_morphism_identity R
          (@comm_ring_freyd_image_presentation R W P Q f))))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)))
    (@comm_ring_presentation_agreement_witness R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_cokernel_presentation R
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
        (@comm_ring_freyd_comparison_cokernel_projection_raw R W P Q f))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)))
      (@comm_ring_freyd_comparison_epimorphism_witness R W P Q f b))
    (@eq_trans _ _ _ _
      (@comm_ring_presentation_agreement_law R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_cokernel_presentation R
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
        (@comm_ring_presentation_morphism_map R
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
          (@comm_ring_freyd_comparison_cokernel_projection_raw R W P Q f))
        (@comm_ring_presentation_morphism_map R
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)
          (@comm_ring_presentation_morphism_zero R
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_comparison_cokernel_presentation R W P Q f)))
        (@comm_ring_freyd_comparison_epimorphism_witness R W P Q f b))
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_cokernel_presentation R
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_image_presentation R W P Q f))),
          @comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_cokernel_presentation R
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_image_presentation R W P Q f)) z
            (@comm_ring_matrix_zero R
              (@comm_ring_presentation_generators R
                (@comm_ring_freyd_cokernel_presentation R
                  (@comm_ring_freyd_coimage_presentation R W P Q f)
                  (@comm_ring_freyd_image_presentation R W P Q f)
                  (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))
              (@comm_ring_presentation_generators R
                (@comm_ring_freyd_image_presentation R W P Q f))))
        _ _
        (@eq_sym _ _ _
          (@comm_ring_matrix_comp_right_identity_path R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_image_presentation R W P Q f))
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_cokernel_presentation R
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))
            (@comm_ring_presentation_morphism_map R
              (@comm_ring_freyd_image_presentation R W P Q f)
              (@comm_ring_freyd_cokernel_presentation R
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
              (@comm_ring_freyd_cokernel_projection_raw R
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))))));

symbol comm_ring_freyd_comparison_epi_identity_test_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingFreydNormalEpiTestAgreement R W
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)
      (@comm_ring_presentation_morphism_identity R
        (@comm_ring_freyd_coimage_presentation R W P Q f)))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_freyd_kernel_presentation R W
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_presentation_morphism_comp R
        (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_presentation_morphism_identity R
          (@comm_ring_freyd_coimage_presentation R W P Q f))
        (@comm_ring_freyd_comparison_kernel_embedding_raw R W P Q f)))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)))
    (@comm_ring_presentation_agreement_witness R
      (@comm_ring_freyd_kernel_presentation R W
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_kernel_embedding_raw R W P Q f))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)))
      (@comm_ring_freyd_comparison_monomorphism_witness R W P Q f b))
    (@eq_trans _ _ _ _
      (@comm_ring_presentation_agreement_law R
        (@comm_ring_freyd_kernel_presentation R W
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_presentation_morphism_map R
          (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_comparison_kernel_embedding_raw R W P Q f))
        (@comm_ring_presentation_morphism_map R
          (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_presentation_morphism_zero R
            (@comm_ring_freyd_comparison_kernel_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f)))
        (@comm_ring_freyd_comparison_monomorphism_witness R W P Q f b))
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_coimage_presentation R W P Q f))
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_kernel_presentation R W
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))),
          @comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_coimage_presentation R W P Q f))
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_kernel_presentation R W
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))) z
            (@comm_ring_matrix_zero R
              (@comm_ring_presentation_generators R
                (@comm_ring_freyd_coimage_presentation R W P Q f))
              (@comm_ring_presentation_generators R
                (@comm_ring_freyd_kernel_presentation R W
                  (@comm_ring_freyd_coimage_presentation R W P Q f)
                  (@comm_ring_freyd_image_presentation R W P Q f)
                  (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))))
        _ _
        (@eq_sym _ _ _
          (@comm_ring_matrix_comp_left_identity_path R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_kernel_presentation R W
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_coimage_presentation R W P Q f))
            (@comm_ring_presentation_morphism_map R
              (@comm_ring_freyd_kernel_presentation R W
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f))
              (@comm_ring_freyd_coimage_presentation R W P Q f)
              (@comm_ring_freyd_kernel_embedding_raw R W
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)))))));

symbol comm_ring_freyd_comparison_inverse_from_mono_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_normal_mono_lift_raw R W
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)
    (@comm_ring_freyd_comparison_monomorphism_witness R W P Q f b)
    (@comm_ring_presentation_morphism_identity R
      (@comm_ring_freyd_image_presentation R W P Q f))
    (@comm_ring_freyd_comparison_mono_identity_test_agreement R W P Q f b);

symbol comm_ring_freyd_comparison_inverse_from_epi_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_normal_epi_colift_raw R W
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)
    (@comm_ring_freyd_comparison_epimorphism_witness R W P Q f b)
    (@comm_ring_presentation_morphism_identity R
      (@comm_ring_freyd_coimage_presentation R W P Q f))
    (@comm_ring_freyd_comparison_epi_identity_test_agreement R W P Q f b);

symbol comm_ring_freyd_comparison_inverse_from_mono
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_comparison_inverse_from_mono_raw R W P Q f b);

symbol comm_ring_freyd_comparison_inverse_from_epi
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_image_presentation R W P Q f)
    (@comm_ring_freyd_coimage_presentation R W P Q f)
    (@comm_ring_freyd_comparison_inverse_from_epi_raw R W P Q f b);

symbol comm_ring_freyd_comparison_right_inverse_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f))
      (@comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_image_comparison R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))
      (@id (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_image_presentation R W P Q f)))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_comp_usability_path R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_image_comparison R W P Q f)
      (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_mono_reconstruction_path R W
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)
        (@comm_ring_freyd_comparison_monomorphism_witness R W P Q f b)
        (@comm_ring_presentation_morphism_identity R
          (@comm_ring_freyd_image_presentation R W P Q f))
        (@comm_ring_freyd_comparison_mono_identity_test_agreement R W P Q f b))
      (@eq_sym _ _ _
        (@comm_ring_freyd_identity_usability_path R
          (@comm_ring_freyd_image_presentation R W P Q f))));

symbol comm_ring_freyd_comparison_epi_left_inverse_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
      (@comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
        (@comm_ring_freyd_coimage_image_comparison R W P Q f))
      (@id (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_coimage_presentation R W P Q f)))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_comp_usability_path R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
      (@comm_ring_freyd_coimage_image_comparison R W P Q f))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_epi_reconstruction_path R W
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_coimage_image_comparison_raw R W P Q f)
        (@comm_ring_freyd_comparison_epimorphism_witness R W P Q f b)
        (@comm_ring_presentation_morphism_identity R
          (@comm_ring_freyd_coimage_presentation R W P Q f))
        (@comm_ring_freyd_comparison_epi_identity_test_agreement R W P Q f b))
      (@eq_sym _ _ _
        (@comm_ring_freyd_identity_usability_path R
          (@comm_ring_freyd_coimage_presentation R W P Q f))));

symbol comm_ring_freyd_comparison_epi_inverse_right_identity_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
      (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
      (@comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
        (@id (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_image_presentation R W P Q f))))
≔ @eq_refl _
    (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b);

symbol comm_ring_freyd_comparison_epi_inverse_replace_right_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
      (@comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
        (@id (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_image_presentation R W P Q f)))
      (@comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
        (@comp_fapp0 (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_image_comparison R W P Q f)
          (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))))
≔ @eq_ap _ _
    (λ z : τ (@CommRingFreydHomSet R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)),
      @comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b) z)
    _ _
    (@eq_sym _ _ _
      (@comm_ring_freyd_comparison_right_inverse_path R W P Q f b));

symbol comm_ring_freyd_comparison_inverse_candidates_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_image_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
      (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
      (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_comparison_epi_inverse_right_identity_path
      R W P Q f b)
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_comparison_epi_inverse_replace_right_path
        R W P Q f b)
      (@eq_trans _ _ _ _
        (@comp_assoc
          (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_comparison_inverse_from_epi R W P Q f b)
          (@comm_ring_freyd_coimage_image_comparison R W P Q f)
          (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))
        (@eq_trans _ _ _ _
          (@eq_ap _ _
            (λ z : τ (@CommRingFreydHomSet R
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_coimage_presentation R W P Q f)),
              @comp_fapp0 (@CommRingFreydPresentation_cat R)
                (@comm_ring_freyd_image_presentation R W P Q f)
                (@comm_ring_freyd_coimage_presentation R W P Q f)
                (@comm_ring_freyd_coimage_presentation R W P Q f) z
                (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))
            _ _
            (@comm_ring_freyd_comparison_epi_left_inverse_path R W P Q f b))
          (@eq_refl _
            (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b)))));

symbol comm_ring_freyd_comparison_left_inverse_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_coimage_presentation R W P Q f))
      (@comp_fapp0 (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f)
        (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b)
        (@comm_ring_freyd_coimage_image_comparison R W P Q f))
      (@id (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_coimage_presentation R W P Q f)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@eq_ap _ _
        (λ z : τ (@CommRingFreydHomSet R
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f)),
          @comp_fapp0 (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f) z
            (@comm_ring_freyd_coimage_image_comparison R W P Q f))
        _ _
        (@comm_ring_freyd_comparison_inverse_candidates_path R W P Q f b)))
    (@comm_ring_freyd_comparison_epi_left_inverse_path R W P Q f b);

symbol comm_ring_freyd_coimage_image_iso
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (b : τ (@CommRingFreydComparisonBimorphismWitness R W P Q f))
  : τ (@IsoEvidence (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f))
≔ @Struct_sigma
    (@CommRingFreydHomSet R
      (@comm_ring_freyd_coimage_presentation R W P Q f)
      (@comm_ring_freyd_image_presentation R W P Q f))
    (λ to : τ _,
      `Σ_ from : τ (@CommRingFreydHomSet R
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)),
      `Σ_ _ : τ (@= (@CommRingFreydHomSet R
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f))
        (@comp_fapp0 (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f) from to)
        (@id (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_coimage_presentation R W P Q f))),
      @= (@CommRingFreydHomSet R
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f))
        (@comp_fapp0 (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_image_presentation R W P Q f)
          (@comm_ring_freyd_coimage_presentation R W P Q f)
          (@comm_ring_freyd_image_presentation R W P Q f) to from)
        (@id (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_image_presentation R W P Q f)))
    (@comm_ring_freyd_coimage_image_comparison R W P Q f)
    (@Struct_sigma
      (@CommRingFreydHomSet R
        (@comm_ring_freyd_image_presentation R W P Q f)
        (@comm_ring_freyd_coimage_presentation R W P Q f))
      (λ from : τ _,
        `Σ_ _ : τ (@= (@CommRingFreydHomSet R
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f))
          (@comp_fapp0 (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f) from
            (@comm_ring_freyd_coimage_image_comparison R W P Q f))
          (@id (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_coimage_presentation R W P Q f))),
        @= (@CommRingFreydHomSet R
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_image_presentation R W P Q f))
          (@comp_fapp0 (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_coimage_image_comparison R W P Q f) from)
          (@id (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_image_presentation R W P Q f)))
      (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b)
      (@Struct_sigma
        (@= (@CommRingFreydHomSet R
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f))
          (@comp_fapp0 (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_image_presentation R W P Q f)
            (@comm_ring_freyd_coimage_presentation R W P Q f)
            (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b)
            (@comm_ring_freyd_coimage_image_comparison R W P Q f))
          (@id (@CommRingFreydPresentation_cat R)
            (@comm_ring_freyd_coimage_presentation R W P Q f)))
        (λ _ : τ _,
          @= (@CommRingFreydHomSet R
              (@comm_ring_freyd_image_presentation R W P Q f)
              (@comm_ring_freyd_image_presentation R W P Q f))
            (@comp_fapp0 (@CommRingFreydPresentation_cat R)
              (@comm_ring_freyd_image_presentation R W P Q f)
              (@comm_ring_freyd_coimage_presentation R W P Q f)
              (@comm_ring_freyd_image_presentation R W P Q f)
              (@comm_ring_freyd_coimage_image_comparison R W P Q f)
              (@comm_ring_freyd_comparison_inverse_from_mono R W P Q f b))
            (@id (@CommRingFreydPresentation_cat R)
              (@comm_ring_freyd_image_presentation R W P Q f)))
        (@comm_ring_freyd_comparison_left_inverse_path R W P Q f b)
        (@comm_ring_freyd_comparison_right_inverse_path R W P Q f b)));
