/*
  Shared witnessed homology over the two actual outgoing-kernel choices.

  The cycle embedding and canonical boundary use the selected kernel core.
  A supplied-boundary introduction also retains a computed raw boundary and
  its reconstruction, then derives the existing cokernel universal package.
  Exactness is epicity of that stored boundary. The W-indexed API delegates
  here; no parallel homology theory, quotient decoder, rule or axiom is added.
*/
require open emdash.emdash3_2_commutative_algebra_freyd_witnessed_abelian;

// The actual outgoing-kernel choices fix the cycle presentation.
symbol comm_ring_freyd_selected_homology_cycle_presentation
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_selected_kernel_presentation R P1 P0 d K;

// Its raw embedding is the existing first weak-pullback projection.
symbol comm_ring_freyd_selected_homology_cycle_embedding_raw
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      P1)
≔ @comm_ring_freyd_selected_kernel_embedding_raw R P1 P0 d K;

// Canonically lift the incoming differential using the original chain agreement.
symbol comm_ring_freyd_selected_homology_boundary_selected_raw
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0))))
  : τ (@CommRingPresentationMorphism R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K))
≔ @comm_ring_freyd_selected_kernel_lift_raw R P1 P0 P2 d K dNext chain;

// Kernel reconstruction retains explicit relation coefficients.
symbol comm_ring_freyd_selected_homology_boundary_selected_reconstruction_agreement
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0))))
  : τ (@CommRingPresentationMorphismAgreement R P2 P1
      (@comm_ring_presentation_morphism_map R P2 P1
        (@comm_ring_presentation_morphism_comp R P2
          (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K) P1
          (@comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d K)
          (@comm_ring_freyd_selected_homology_boundary_selected_raw R P2 P1 P0 dNext d K chain)))
      (@comm_ring_presentation_morphism_map R P2 P1 dNext))
≔ @comm_ring_freyd_selected_kernel_reconstruction_agreement R P1 P0 P2 d K dNext chain;

// Whole homology: raw boundary, its reconstruction, and its witnessed cokernel.
symbol CommRingFreydSelectedHomologyAt
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0))))
  : Grpd
≔ `Σ_ boundary : τ (@CommRingPresentationMorphism R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)),
   @Product_grpd
      (@CommRingPresentationMorphismAgreement R P2 P1
        (@comm_ring_presentation_morphism_map R P2 P1
          (@comm_ring_presentation_morphism_comp R P2
            (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K) P1
            (@comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d K)
            boundary))
        (@comm_ring_presentation_morphism_map R P2 P1 dNext))
      (@CommRingFreydWitnessedCokernelUniversal R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        boundary);

// Retain an already-computed raw boundary; derive its original cokernel universal.
symbol comm_ring_freyd_selected_homology_from_boundary
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0))))
  (boundaryGiven : τ (@CommRingPresentationMorphism R P2 (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)))
  (reconstructionGiven : τ (@CommRingPresentationMorphismAgreement R P2 P1
    (@comm_ring_presentation_morphism_map R P2 P1
      (@comm_ring_presentation_morphism_comp R P2 (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K) P1
        (@comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d K) boundaryGiven))
    (@comm_ring_presentation_morphism_map R P2 P1 dNext)))
  : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain)
≔ @Struct_sigma
    (@CommRingPresentationMorphism R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K))
    (λ boundary : τ (@CommRingPresentationMorphism R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)),
      @Product_grpd
        (@CommRingPresentationMorphismAgreement R P2 P1
          (@comm_ring_presentation_morphism_map R P2 P1
            (@comm_ring_presentation_morphism_comp R P2
              (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K) P1
              (@comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d K)
              boundary))
          (@comm_ring_presentation_morphism_map R P2 P1 dNext))
        (@CommRingFreydWitnessedCokernelUniversal R P2
          (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
          boundary))
    boundaryGiven
    (@Product_pair_grpd _ _
      reconstructionGiven
      (@comm_ring_freyd_witnessed_cokernel_universal R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        boundaryGiven));

// Canonical construction delegates to the supplied-boundary introduction.
symbol comm_ring_freyd_selected_witnessed_homology_at
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0))))
  : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain)
≔ @comm_ring_freyd_selected_homology_from_boundary R P2 P1 P0 dNext d K chain
    (@comm_ring_freyd_selected_homology_boundary_selected_raw R P2 P1 P0 dNext d K chain)
    (@comm_ring_freyd_selected_homology_boundary_selected_reconstruction_agreement R P2 P1 P0 dNext d K chain);

// Observations retain the actual boundary and its original reconstruction.
symbol comm_ring_freyd_selected_homology_boundary_raw
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingPresentationMorphism R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K))
≔ sigma_Fst H;

symbol comm_ring_freyd_selected_homology_boundary_reconstruction_agreement
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingPresentationMorphismAgreement R P2 P1
      (@comm_ring_presentation_morphism_map R P2 P1
        (@comm_ring_presentation_morphism_comp R P2
          (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K) P1
          (@comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d K)
          (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H)))
      (@comm_ring_presentation_morphism_map R P2 P1 dNext))
≔ sigma_Fst (sigma_Snd H);

// The whole cokernel factor family is retained, not replaced by sample factors.
symbol comm_ring_freyd_selected_homology_cokernel_universal
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingFreydWitnessedCokernelUniversal R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H))
≔ sigma_Snd (sigma_Snd H);

// Homology and its projection reuse the cokernel of the stored boundary.
symbol comm_ring_freyd_selected_homology_presentation
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_cokernel_presentation R P2
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H);

symbol comm_ring_freyd_selected_homology_projection_raw
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
≔ @comm_ring_freyd_cokernel_projection_raw R P2
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H);

// The original cokernel supplies the raw projection-annihilation agreement.
symbol comm_ring_freyd_selected_homology_projection_annihilation_agreement
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingPresentationMorphismAgreement R P2
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
      (@comm_ring_presentation_morphism_map R P2
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
        (@comm_ring_presentation_morphism_comp R P2
          (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
          (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
          (@comm_ring_freyd_selected_homology_projection_raw R P2 P1 P0 dNext d K chain H)
          (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H)))
      (@comm_ring_presentation_morphism_map R P2
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
        (@comm_ring_presentation_morphism_zero R P2
          (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))))
≔ @comm_ring_freyd_cokernel_annihilation_agreement R P2
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H);

// Exactness is epicity of the stored boundary at these same cycle choices.
symbol CommRingFreydSelectedExactnessAt
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : Grpd
≔ @CommRingFreydEpimorphismWitness R P2
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H);

symbol comm_ring_freyd_selected_exactness_projection_zero_agreement
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  [H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain)]
  (exact : τ (@CommRingFreydSelectedExactnessAt R P2 P1 P0 dNext d K chain H))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
        (@comm_ring_freyd_selected_homology_projection_raw R P2 P1 P0 dNext d K chain H))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
          (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))))
≔ exact;

// Quotient observations retain the classes of the stored raw arrows.
symbol comm_ring_freyd_selected_homology_boundary
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingFreydHomSet R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K))
≔ @comm_ring_freyd_hom_class R P2
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H);

symbol comm_ring_freyd_selected_homology_projection
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
    (@comm_ring_freyd_selected_homology_projection_raw R P2 P1 P0 dNext d K chain H);

// Pass the retained raw reconstruction agreement to its quotient path.
symbol comm_ring_freyd_selected_homology_boundary_reconstruction_path
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@= (@CommRingFreydHomSet R P2 P1)
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        P1
        (@comm_ring_freyd_selected_kernel_embedding R P1 P0 d K)
        (@comm_ring_freyd_selected_homology_boundary R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_hom_class R P2 P1 dNext))
≔ @comm_ring_freyd_agreement_path R P2 P1
    (@comm_ring_presentation_morphism_comp R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      P1
      (@comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H))
    dNext
    (@comm_ring_freyd_selected_homology_boundary_reconstruction_agreement R P2 P1 P0 dNext d K chain H);

// The quotient projection kills the original stored boundary.
symbol comm_ring_freyd_selected_homology_projection_annihilation_path
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  : τ (@= (@CommRingFreydHomSet R P2
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
        (@comm_ring_freyd_selected_homology_projection R P2 P1 P0 dNext d K chain H)
        (@comm_ring_freyd_selected_homology_boundary R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_zero_class R P2
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)))
≔ @comm_ring_freyd_agreement_path R P2
    (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
    (@comm_ring_presentation_morphism_comp R P2
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
      (@comm_ring_freyd_selected_homology_projection_raw R P2 P1 P0 dNext d K chain H)
      (@comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain H))
    (@comm_ring_presentation_morphism_zero R P2
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
    (@comm_ring_freyd_selected_homology_projection_annihilation_agreement R P2 P1 P0 dNext d K chain H);

// An epic stored boundary makes its homology projection zero in the quotient.
symbol comm_ring_freyd_selected_exactness_projection_zero_path
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [K : τ (@CommRingFreydKernelChoices R P1 P0 d)]
  [chain : τ (@CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0)))]
  [H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain)]
  (exact : τ (@CommRingFreydSelectedExactnessAt R P2 P1 P0 dNext d K chain H))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_selected_homology_projection R P2 P1 P0 dNext d K chain H)
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)))
≔ @comm_ring_freyd_agreement_path R
    (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
    (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
    (@comm_ring_freyd_selected_homology_projection_raw R P2 P1 P0 dNext d K chain H)
    (@comm_ring_presentation_morphism_zero R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
    (@comm_ring_freyd_selected_exactness_projection_zero_agreement R P2 P1 P0 dNext d K chain H exact);
