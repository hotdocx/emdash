/*
  Per-arrow selected data for the two-weak-pullback Freyd kernel construction.

  The second whole weak pullback depends on the actual first package.
  Its first projection presents the kernel relations; the first package's
  first projection is the embedding datum. No global weak-kernel selector,
  rank cast, object transport, or new universal operation is required.
  Kernel embedding, annihilation, lifting, and uniqueness are downstream.
*/

require open emdash.emdash3_2_commutative_algebra_finite_free_weak_pullbacks;
require open emdash.emdash3_2_commutative_algebra_presentations;

// First choice: weak pullback of the raw datum and target relation matrix.
symbol CommRingFreydKernelFirstChoice [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q)) : Grpd
≔ @CommRingFiniteFreeWeakPullback R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q);

symbol comm_ring_freyd_kernel_first_choice_rank [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (U : τ (@CommRingFreydKernelFirstChoice R P Q f)) : τ Nat_grpd
≔ @comm_ring_finite_free_weak_pullback_rank R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q) U;

symbol comm_ring_freyd_kernel_first_choice_projection [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (U : τ (@CommRingFreydKernelFirstChoice R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_presentation_generators R P)
    (@comm_ring_freyd_kernel_first_choice_rank R P Q f U))
≔ @comm_ring_finite_free_weak_pullback_proj1 R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q) U;

// Second choice depends on that very first package and its projection.
symbol CommRingFreydKernelSecondChoice [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (U : τ (@CommRingFreydKernelFirstChoice R P Q f)) : Grpd
≔ @CommRingFiniteFreeWeakPullback R
    (@comm_ring_freyd_kernel_first_choice_rank R P Q f U)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_choice_projection R P Q f U)
    (@comm_ring_presentation_matrix R P);

symbol CommRingFreydKernelChoices [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q)) : Grpd
≔ `Σ_ U : τ (@CommRingFreydKernelFirstChoice R P Q f),
     @CommRingFreydKernelSecondChoice R P Q f U;

symbol comm_ring_freyd_kernel_choices_intro [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (U : τ (@CommRingFreydKernelFirstChoice R P Q f))
  (V : τ (@CommRingFreydKernelSecondChoice R P Q f U))
  : τ (@CommRingFreydKernelChoices R P Q f)
≔ @Struct_sigma (@CommRingFreydKernelFirstChoice R P Q f)
    (λ U0 : τ (@CommRingFreydKernelFirstChoice R P Q f),
      @CommRingFreydKernelSecondChoice R P Q f U0) U V;

symbol comm_ring_freyd_kernel_choices_first [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingFreydKernelFirstChoice R P Q f)
≔ sigma_Fst K;

symbol comm_ring_freyd_kernel_choices_second [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingFreydKernelSecondChoice R P Q f
    (@comm_ring_freyd_kernel_choices_first R P Q f K))
≔ sigma_Snd K;

symbol comm_ring_freyd_selected_kernel_rank [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f)) : τ Nat_grpd
≔ @comm_ring_freyd_kernel_first_choice_rank R P Q f
    (@comm_ring_freyd_kernel_choices_first R P Q f K);

// Underlying matrix of the eventual raw kernel embedding, at its actual rank.
symbol comm_ring_freyd_selected_kernel_projection [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_presentation_generators R P)
    (@comm_ring_freyd_selected_kernel_rank R P Q f K))
≔ @comm_ring_freyd_kernel_first_choice_projection R P Q f
    (@comm_ring_freyd_kernel_choices_first R P Q f K);

symbol comm_ring_freyd_selected_kernel_relation_rank [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f)) : τ Nat_grpd
≔ @comm_ring_finite_free_weak_pullback_rank R
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_choices_second R P Q f K);

symbol comm_ring_freyd_selected_kernel_relation_matrix [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingMatrix R (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K))
≔ @comm_ring_finite_free_weak_pullback_proj1 R
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_selected_kernel_projection R P Q f K)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_freyd_kernel_choices_second R P Q f K);

symbol comm_ring_freyd_selected_kernel_presentation [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (K : τ (@CommRingFreydKernelChoices R P Q f))
  : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R
    (@comm_ring_freyd_selected_kernel_rank R P Q f K)
    (@comm_ring_freyd_selected_kernel_relation_rank R P Q f K)
    (@comm_ring_freyd_selected_kernel_relation_matrix R P Q f K);
