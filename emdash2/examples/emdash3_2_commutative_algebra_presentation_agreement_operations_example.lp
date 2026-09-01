/* Reviewer-facing presentation-agreement algebra consumer. */

require open emdash.emdash3_2_commutative_algebra_presentation_agreement_operations;

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (F : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
  ⊢ @comm_ring_presentation_agreement_witness R P Q F F
      (@comm_ring_presentation_agreement_refl R P Q F)
  ≡ @comm_ring_matrix_zero R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P);

assert
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  ⊢ @comm_ring_presentation_agreement_witness R P Q G F
      (@comm_ring_presentation_agreement_sym R P Q F G a)
  ≡ @comm_ring_matrix_neg R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_agreement_witness R P Q F G a);

symbol presentation_agreement_precomp_reviewer
  [R : τ CommRing]
  [O P Q : τ (@CommRingPresentation R)]
  [F F' : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F F'))
  (K : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R O)))
  : τ (@CommRingPresentationMorphismAgreement R O Q
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R O) F K)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R O) F' K))
≔ @comm_ring_presentation_agreement_precomp R O P Q F F' a K;

symbol presentation_agreement_postcomp_reviewer
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  [F F' : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F F'))
  (g : τ (@CommRingPresentationMorphism R Q S))
  : τ (@CommRingPresentationMorphismAgreement R P S
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R S)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R Q S g) F)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R S)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R Q S g) F'))
≔ @comm_ring_presentation_agreement_postcomp R P Q S F F' a g;

symbol presentation_agreement_neg_reviewer
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_matrix_neg R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P) F)
      (@comm_ring_matrix_neg R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P) G))
≔ @comm_ring_presentation_agreement_neg R P Q F G a;

assertnot
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (F G : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)))
  (a : τ (@CommRingPresentationMorphismAgreement R P Q F G))
  ⊢ @comm_ring_presentation_agreement_witness R P Q G F
      (@comm_ring_presentation_agreement_sym R P Q F G a)
  ≡ @comm_ring_presentation_agreement_witness R P Q F G a;
