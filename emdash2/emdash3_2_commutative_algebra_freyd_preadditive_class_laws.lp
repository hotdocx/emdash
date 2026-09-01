/*
  Preadditive laws on the generating raw classes of each Freyd quotient Hom.

  A literal equality of generator matrices induces target-factorization
  agreement by path induction. Groupoidification and truncation then turn that
  agreement into equality of ordinary Hom classes. The resulting laws cover
  additive unit, associativity, commutativity, inverse, and both composition
  distributivity orientations on all raw presentation classes. Extension to
  arbitrary quotient points requires a separately identified dependent/
  proposition-valued groupoidification induction interface.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_usability;

symbol comm_ring_freyd_class_map_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingPresentationMorphism R P Q))
  (p : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g)))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_hom_class R P Q f)
      (@comm_ring_freyd_hom_class R P Q g))
≔ @comm_ring_freyd_agreement_path R P Q f g
    (@comm_ring_presentation_agreement_of_map_path R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g)
      p);

symbol comm_ring_freyd_add_zero_right_class_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_zero_class R P Q))
      (@comm_ring_freyd_hom_class R P Q f))
≔ @comm_ring_freyd_class_map_path R P Q
    (@comm_ring_presentation_morphism_add R P Q f
      (@comm_ring_presentation_morphism_zero R P Q))
    f
    (@comm_ring_matrix_add_zero_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f));

symbol comm_ring_freyd_add_zero_left_class_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_zero_class R P Q)
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_hom_class R P Q f))
≔ @comm_ring_freyd_class_map_path R P Q
    (@comm_ring_presentation_morphism_add R P Q
      (@comm_ring_presentation_morphism_zero R P Q) f)
    f
    (@comm_ring_matrix_add_zero_left_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f));

symbol comm_ring_freyd_add_assoc_class_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g h : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_add R P Q
          (@comm_ring_freyd_hom_class R P Q f)
          (@comm_ring_freyd_hom_class R P Q g))
        (@comm_ring_freyd_hom_class R P Q h))
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_add R P Q
          (@comm_ring_freyd_hom_class R P Q g)
          (@comm_ring_freyd_hom_class R P Q h))))
≔ @comm_ring_freyd_class_map_path R P Q
    (@comm_ring_presentation_morphism_add R P Q
      (@comm_ring_presentation_morphism_add R P Q f g) h)
    (@comm_ring_presentation_morphism_add R P Q f
      (@comm_ring_presentation_morphism_add R P Q g h))
    (@comm_ring_matrix_add_assoc_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g)
      (@comm_ring_presentation_morphism_map R P Q h));

symbol comm_ring_freyd_add_comm_class_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_hom_class R P Q g))
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q g)
        (@comm_ring_freyd_hom_class R P Q f)))
≔ @comm_ring_freyd_class_map_path R P Q
    (@comm_ring_presentation_morphism_add R P Q f g)
    (@comm_ring_presentation_morphism_add R P Q g f)
    (@comm_ring_matrix_add_comm_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g));

symbol comm_ring_freyd_add_inv_class_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_neg R P Q
          (@comm_ring_freyd_hom_class R P Q f)))
      (@comm_ring_freyd_zero_class R P Q))
≔ @comm_ring_freyd_class_map_path R P Q
    (@comm_ring_presentation_morphism_add R P Q f
      (@comm_ring_presentation_morphism_neg R P Q f))
    (@comm_ring_presentation_morphism_zero R P Q)
    (@comm_ring_matrix_add_inv_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f));

symbol comm_ring_freyd_comp_add_right_class_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (h : τ (@CommRingPresentationMorphism R Q S))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@comm_ring_freyd_hom_class R Q S h)
        (@comm_ring_freyd_add R P Q
          (@comm_ring_freyd_hom_class R P Q f)
          (@comm_ring_freyd_hom_class R P Q g)))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S
          (@comm_ring_freyd_hom_class R Q S h)
          (@comm_ring_freyd_hom_class R P Q f))
        (@comm_ring_freyd_comp R P Q S
          (@comm_ring_freyd_hom_class R Q S h)
          (@comm_ring_freyd_hom_class R P Q g))))
≔ @comm_ring_freyd_class_map_path R P S
    (@comm_ring_presentation_morphism_comp R P Q S h
      (@comm_ring_presentation_morphism_add R P Q f g))
    (@comm_ring_presentation_morphism_add R P S
      (@comm_ring_presentation_morphism_comp R P Q S h f)
      (@comm_ring_presentation_morphism_comp R P Q S h g))
    (@comm_ring_matrix_comp_add_right_path R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R Q S h)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g));

symbol comm_ring_freyd_comp_add_left_class_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g h : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@comm_ring_freyd_add R Q S
          (@comm_ring_freyd_hom_class R Q S g)
          (@comm_ring_freyd_hom_class R Q S h))
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S
          (@comm_ring_freyd_hom_class R Q S g)
          (@comm_ring_freyd_hom_class R P Q f))
        (@comm_ring_freyd_comp R P Q S
          (@comm_ring_freyd_hom_class R Q S h)
          (@comm_ring_freyd_hom_class R P Q f))))
≔ @comm_ring_freyd_class_map_path R P S
    (@comm_ring_presentation_morphism_comp R P Q S
      (@comm_ring_presentation_morphism_add R Q S g h) f)
    (@comm_ring_presentation_morphism_add R P S
      (@comm_ring_presentation_morphism_comp R P Q S g f)
      (@comm_ring_presentation_morphism_comp R P Q S h f))
    (@comm_ring_matrix_comp_add_left_path R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R Q S g)
      (@comm_ring_presentation_morphism_map R Q S h)
      (@comm_ring_presentation_morphism_map R P Q f));

// Homwise computational operations, without an overclaim about all laws.
symbol CommRingFreydAdditiveHomOperations
  (R : τ CommRing)
  : Grpd
≔ @Pi_grpd (@CommRingPresentation R)
    (λ P : τ (@CommRingPresentation R),
      @Pi_grpd (@CommRingPresentation R)
        (λ Q : τ (@CommRingPresentation R),
          `Σ_ zero_map : τ (@CommRingFreydHomSet R P Q),
            @Product_grpd
              (@Function_grpd
                (@CommRingFreydHomSet R P Q)
                (@Function_grpd
                  (@CommRingFreydHomSet R P Q)
                  (@CommRingFreydHomSet R P Q)))
              (@Function_grpd
                (@CommRingFreydHomSet R P Q)
                (@CommRingFreydHomSet R P Q))));

symbol comm_ring_freyd_additive_hom_operations
  (R : τ CommRing)
  : τ (@CommRingFreydAdditiveHomOperations R)
≔ λ P : τ (@CommRingPresentation R),
    λ Q : τ (@CommRingPresentation R),
      @Struct_sigma
        (@CommRingFreydHomSet R P Q)
        (λ _ : τ (@CommRingFreydHomSet R P Q),
          @Product_grpd
            (@Function_grpd
              (@CommRingFreydHomSet R P Q)
              (@Function_grpd
                (@CommRingFreydHomSet R P Q)
                (@CommRingFreydHomSet R P Q)))
            (@Function_grpd
              (@CommRingFreydHomSet R P Q)
              (@CommRingFreydHomSet R P Q)))
        (@comm_ring_freyd_zero_class R P Q)
        (@Product_pair_grpd
          (@Function_grpd
            (@CommRingFreydHomSet R P Q)
            (@Function_grpd
              (@CommRingFreydHomSet R P Q)
              (@CommRingFreydHomSet R P Q)))
          (@Function_grpd
            (@CommRingFreydHomSet R P Q)
            (@CommRingFreydHomSet R P Q))
          (λ f : τ (@CommRingFreydHomSet R P Q),
            λ g : τ (@CommRingFreydHomSet R P Q),
              @comm_ring_freyd_add R P Q f g)
          (λ f : τ (@CommRingFreydHomSet R P Q),
            @comm_ring_freyd_neg R P Q f));

// Exact law package presently proved on every generating raw class.
symbol CommRingFreydClassPreadditiveEvidence
  (R : τ CommRing)
  : Grpd
≔ @Product_grpd
    (@Pi_grpd (@CommRingPresentation R) (λ P : τ _,
      @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
        @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
          @= (@CommRingFreydHomSet R P Q)
            (@comm_ring_freyd_add R P Q
              (@comm_ring_freyd_hom_class R P Q f)
              (@comm_ring_freyd_zero_class R P Q))
            (@comm_ring_freyd_hom_class R P Q f)))))
    (@Product_grpd
      (@Pi_grpd (@CommRingPresentation R) (λ P : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
          @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
            @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ g : τ _,
              @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ h : τ _,
                @= (@CommRingFreydHomSet R P Q)
                  (@comm_ring_freyd_add R P Q
                    (@comm_ring_freyd_add R P Q
                      (@comm_ring_freyd_hom_class R P Q f)
                      (@comm_ring_freyd_hom_class R P Q g))
                    (@comm_ring_freyd_hom_class R P Q h))
                  (@comm_ring_freyd_add R P Q
                    (@comm_ring_freyd_hom_class R P Q f)
                    (@comm_ring_freyd_add R P Q
                      (@comm_ring_freyd_hom_class R P Q g)
                      (@comm_ring_freyd_hom_class R P Q h)))))))))
      (@Product_grpd
        (@Pi_grpd (@CommRingPresentation R) (λ P : τ _,
          @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
            @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
              @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ g : τ _,
                @= (@CommRingFreydHomSet R P Q)
                  (@comm_ring_freyd_add R P Q
                    (@comm_ring_freyd_hom_class R P Q f)
                    (@comm_ring_freyd_hom_class R P Q g))
                  (@comm_ring_freyd_add R P Q
                    (@comm_ring_freyd_hom_class R P Q g)
                    (@comm_ring_freyd_hom_class R P Q f)))))))
        (@Product_grpd
          (@Pi_grpd (@CommRingPresentation R) (λ P : τ _,
            @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
              @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
                @= (@CommRingFreydHomSet R P Q)
                  (@comm_ring_freyd_add R P Q
                    (@comm_ring_freyd_hom_class R P Q f)
                    (@comm_ring_freyd_neg R P Q
                      (@comm_ring_freyd_hom_class R P Q f)))
                  (@comm_ring_freyd_zero_class R P Q)))))
          (@Product_grpd
            (@Pi_grpd (@CommRingPresentation R) (λ P : τ _,
              @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
                @Pi_grpd (@CommRingPresentation R) (λ S : τ _,
                  @Pi_grpd (@CommRingPresentationMorphism R Q S) (λ h : τ _,
                    @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
                      @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ g : τ _,
                        @= (@CommRingFreydHomSet R P S)
                          (@comm_ring_freyd_comp R P Q S
                            (@comm_ring_freyd_hom_class R Q S h)
                            (@comm_ring_freyd_add R P Q
                              (@comm_ring_freyd_hom_class R P Q f)
                              (@comm_ring_freyd_hom_class R P Q g)))
                          (@comm_ring_freyd_add R P S
                            (@comm_ring_freyd_comp R P Q S
                              (@comm_ring_freyd_hom_class R Q S h)
                              (@comm_ring_freyd_hom_class R P Q f))
                            (@comm_ring_freyd_comp R P Q S
                              (@comm_ring_freyd_hom_class R Q S h)
                              (@comm_ring_freyd_hom_class R P Q g))))))))))
            (@Pi_grpd (@CommRingPresentation R) (λ P : τ _,
              @Pi_grpd (@CommRingPresentation R) (λ Q : τ _,
                @Pi_grpd (@CommRingPresentation R) (λ S : τ _,
                  @Pi_grpd (@CommRingPresentationMorphism R Q S) (λ g : τ _,
                    @Pi_grpd (@CommRingPresentationMorphism R Q S) (λ h : τ _,
                      @Pi_grpd (@CommRingPresentationMorphism R P Q) (λ f : τ _,
                        @= (@CommRingFreydHomSet R P S)
                          (@comm_ring_freyd_comp R P Q S
                            (@comm_ring_freyd_add R Q S
                              (@comm_ring_freyd_hom_class R Q S g)
                              (@comm_ring_freyd_hom_class R Q S h))
                            (@comm_ring_freyd_hom_class R P Q f))
                          (@comm_ring_freyd_add R P S
                            (@comm_ring_freyd_comp R P Q S
                              (@comm_ring_freyd_hom_class R Q S g)
                              (@comm_ring_freyd_hom_class R P Q f))
                            (@comm_ring_freyd_comp R P Q S
                              (@comm_ring_freyd_hom_class R Q S h)
                              (@comm_ring_freyd_hom_class R P Q f))))))))))))));

symbol comm_ring_freyd_class_preadditive_evidence
  (R : τ CommRing)
  : τ (@CommRingFreydClassPreadditiveEvidence R)
≔ @Product_pair_grpd _ _
    (λ P : τ _, λ Q : τ _, λ f : τ _,
      @comm_ring_freyd_add_zero_right_class_path R P Q f)
    (@Product_pair_grpd _ _
      (λ P : τ _, λ Q : τ _, λ f : τ _, λ g : τ _, λ h : τ _,
        @comm_ring_freyd_add_assoc_class_path R P Q f g h)
      (@Product_pair_grpd _ _
        (λ P : τ _, λ Q : τ _, λ f : τ _, λ g : τ _,
          @comm_ring_freyd_add_comm_class_path R P Q f g)
        (@Product_pair_grpd _ _
          (λ P : τ _, λ Q : τ _, λ f : τ _,
            @comm_ring_freyd_add_inv_class_path R P Q f)
          (@Product_pair_grpd _ _
            (λ P : τ _, λ Q : τ _, λ S : τ _,
              λ h : τ _, λ f : τ _, λ g : τ _,
                @comm_ring_freyd_comp_add_right_class_path R P Q S h f g)
            (λ P : τ _, λ Q : τ _, λ S : τ _,
              λ g : τ _, λ h : τ _, λ f : τ _,
                @comm_ring_freyd_comp_add_left_class_path R P Q S g h f)))));
