/*
  Capability-indexed formal Freyd snake normal factors.

  The upstream fiber-product, pushout, epic/monic, and normal-test agreements
  remain explicit proof-CAS inputs. Existing witnessed normality selects the
  two raw factors and their quotient reconstruction paths. No quotient decoder,
  closed Abelian instance, runtime rule, or opaque connecting map is added.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_witnessed_abelian;

symbol comm_ring_freyd_snake_u_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  : τ (@CommRingPresentationMorphism R G U)
≔ @comm_ring_freyd_normal_epi_colift_raw R W F G U
    p1 p1_epic middle p1_test;

symbol comm_ring_freyd_snake_u
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  : τ (@CommRingFreydHomSet R G U)
≔ @comm_ring_freyd_normal_epi_colift R W F G U
    p1 p1_epic middle p1_test;

symbol comm_ring_freyd_snake_u_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  : τ (@CommRingPresentationMorphismAgreement R F U
      (@comm_ring_presentation_morphism_map R F U
        (@comm_ring_presentation_morphism_comp R F G U
          (@comm_ring_freyd_snake_u_raw R W F G U
            p1 p1_epic middle p1_test)
          p1))
      (@comm_ring_presentation_morphism_map R F U middle))
≔ @comm_ring_freyd_normal_epi_reconstruction_agreement R W F G U
    p1 p1_epic middle p1_test;

symbol comm_ring_freyd_snake_u_reconstruction_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  : τ (@= (@CommRingFreydHomSet R F U)
      (@comm_ring_freyd_comp R F G U
        (@comm_ring_freyd_snake_u R W F G U
          p1 p1_epic middle p1_test)
        (@comm_ring_freyd_hom_class R F G p1))
      (@comm_ring_freyd_hom_class R F U middle))
≔ @comm_ring_freyd_normal_epi_reconstruction_path R W F G U
    p1 p1_epic middle p1_test;

symbol comm_ring_freyd_snake_connecting_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U H : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  : τ (@CommRingPresentationMorphism R G H)
≔ @comm_ring_freyd_normal_mono_lift_raw R W H U G
    q2 q2_monic
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)
    q2_test;

symbol comm_ring_freyd_snake_connecting
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U H : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  : τ (@CommRingFreydHomSet R G H)
≔ @comm_ring_freyd_normal_mono_lift R W H U G
    q2 q2_monic
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)
    q2_test;

symbol comm_ring_freyd_snake_connecting_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U H : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  : τ (@CommRingPresentationMorphismAgreement R G U
      (@comm_ring_presentation_morphism_map R G U
        (@comm_ring_presentation_morphism_comp R G H U q2
          (@comm_ring_freyd_snake_connecting_raw R W F G U H
            p1 p1_epic middle p1_test q2 q2_monic q2_test)))
      (@comm_ring_presentation_morphism_map R G U
        (@comm_ring_freyd_snake_u_raw R W F G U
          p1 p1_epic middle p1_test)))
≔ @comm_ring_freyd_normal_mono_reconstruction_agreement R W H U G
    q2 q2_monic
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)
    q2_test;

symbol comm_ring_freyd_snake_connecting_reconstruction_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U H : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  : τ (@= (@CommRingFreydHomSet R G U)
      (@comm_ring_freyd_comp R G H U
        (@comm_ring_freyd_hom_class R H U q2)
        (@comm_ring_freyd_snake_connecting R W F G U H
          p1 p1_epic middle p1_test q2 q2_monic q2_test))
      (@comm_ring_freyd_snake_u R W F G U
        p1 p1_epic middle p1_test))
≔ @comm_ring_freyd_normal_mono_reconstruction_path R W H U G
    q2 q2_monic
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)
    q2_test;

symbol CommRingFreydWitnessedSnakeConnecting
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U H : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  : Grpd
≔ `Σ_ u : τ (@CommRingPresentationMorphism R G U),
   @Product_grpd
      (@CommRingPresentationMorphismAgreement R F U
        (@comm_ring_presentation_morphism_map R F U
          (@comm_ring_presentation_morphism_comp R F G U u p1))
        (@comm_ring_presentation_morphism_map R F U middle))
      (`Σ_ partial : τ (@CommRingPresentationMorphism R G H),
        @CommRingPresentationMorphismAgreement R G U
          (@comm_ring_presentation_morphism_map R G U
            (@comm_ring_presentation_morphism_comp R G H U q2 partial))
          (@comm_ring_presentation_morphism_map R G U u));

symbol comm_ring_freyd_witnessed_snake_connecting
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [F G U H : τ (@CommRingPresentation R)]
  (p1 : τ (@CommRingPresentationMorphism R F G))
  (p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1))
  (middle : τ (@CommRingPresentationMorphism R F U))
  (p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle))
  (q2 : τ (@CommRingPresentationMorphism R H U))
  (q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2))
  (q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)))
  : τ (@CommRingFreydWitnessedSnakeConnecting R W F G U H
      p1 p1_epic middle p1_test q2 q2_monic q2_test)
≔ @Struct_sigma
    (@CommRingPresentationMorphism R G U)
    (λ u : τ (@CommRingPresentationMorphism R G U),
      @Product_grpd
        (@CommRingPresentationMorphismAgreement R F U
          (@comm_ring_presentation_morphism_map R F U
            (@comm_ring_presentation_morphism_comp R F G U u p1))
          (@comm_ring_presentation_morphism_map R F U middle))
        (`Σ_ partial : τ (@CommRingPresentationMorphism R G H),
          @CommRingPresentationMorphismAgreement R G U
            (@comm_ring_presentation_morphism_map R G U
              (@comm_ring_presentation_morphism_comp R G H U q2 partial))
            (@comm_ring_presentation_morphism_map R G U u)))
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test)
    (@Product_pair_grpd _ _
      (@comm_ring_freyd_snake_u_reconstruction_agreement R W F G U
        p1 p1_epic middle p1_test)
      (@Struct_sigma
        (@CommRingPresentationMorphism R G H)
        (λ partial : τ (@CommRingPresentationMorphism R G H),
          @CommRingPresentationMorphismAgreement R G U
            (@comm_ring_presentation_morphism_map R G U
              (@comm_ring_presentation_morphism_comp R G H U q2 partial))
            (@comm_ring_presentation_morphism_map R G U
              (@comm_ring_freyd_snake_u_raw R W F G U
                p1 p1_epic middle p1_test)))
        (@comm_ring_freyd_snake_connecting_raw R W F G U H
          p1 p1_epic middle p1_test q2 q2_monic q2_test)
        (@comm_ring_freyd_snake_connecting_reconstruction_agreement R W
          F G U H p1 p1_epic middle p1_test q2 q2_monic q2_test)));

symbol comm_ring_freyd_witnessed_snake_u_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [F G U H : τ (@CommRingPresentation R)]
  [p1 : τ (@CommRingPresentationMorphism R F G)]
  [p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1)]
  [middle : τ (@CommRingPresentationMorphism R F U)]
  [p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle)]
  [q2 : τ (@CommRingPresentationMorphism R H U)]
  [q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2)]
  [q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test))]
  (S : τ (@CommRingFreydWitnessedSnakeConnecting R W F G U H
    p1 p1_epic middle p1_test q2 q2_monic q2_test))
  : τ (@CommRingPresentationMorphism R G U)
≔ sigma_Fst S;

symbol comm_ring_freyd_witnessed_snake_u_reconstruction_agreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [F G U H : τ (@CommRingPresentation R)]
  [p1 : τ (@CommRingPresentationMorphism R F G)]
  [p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1)]
  [middle : τ (@CommRingPresentationMorphism R F U)]
  [p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle)]
  [q2 : τ (@CommRingPresentationMorphism R H U)]
  [q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2)]
  [q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test))]
  (S : τ (@CommRingFreydWitnessedSnakeConnecting R W F G U H
    p1 p1_epic middle p1_test q2 q2_monic q2_test))
  : τ (@CommRingPresentationMorphismAgreement R F U
      (@comm_ring_presentation_morphism_map R F U
        (@comm_ring_presentation_morphism_comp R F G U
          (@comm_ring_freyd_witnessed_snake_u_raw R W F G U H
            p1 p1_epic middle p1_test q2 q2_monic q2_test S)
          p1))
      (@comm_ring_presentation_morphism_map R F U middle))
≔ sigma_Fst (sigma_Snd S);

symbol comm_ring_freyd_witnessed_snake_connecting_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [F G U H : τ (@CommRingPresentation R)]
  [p1 : τ (@CommRingPresentationMorphism R F G)]
  [p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1)]
  [middle : τ (@CommRingPresentationMorphism R F U)]
  [p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle)]
  [q2 : τ (@CommRingPresentationMorphism R H U)]
  [q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2)]
  [q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test))]
  (S : τ (@CommRingFreydWitnessedSnakeConnecting R W F G U H
    p1 p1_epic middle p1_test q2 q2_monic q2_test))
  : τ (@CommRingPresentationMorphism R G H)
≔ sigma_Fst (sigma_Snd (sigma_Snd S));

symbol comm_ring_freyd_witnessed_snake_connecting_reconstruction_agreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [F G U H : τ (@CommRingPresentation R)]
  [p1 : τ (@CommRingPresentationMorphism R F G)]
  [p1_epic : τ (@CommRingFreydEpimorphismWitness R F G p1)]
  [middle : τ (@CommRingPresentationMorphism R F U)]
  [p1_test : τ (@CommRingFreydNormalEpiTestAgreement
    R W F G U p1 middle)]
  [q2 : τ (@CommRingPresentationMorphism R H U)]
  [q2_monic : τ (@CommRingFreydMonomorphismWitness R W H U q2)]
  [q2_test : τ (@CommRingFreydNormalMonoTestAgreement R H U G q2
    (@comm_ring_freyd_snake_u_raw R W F G U
      p1 p1_epic middle p1_test))]
  (S : τ (@CommRingFreydWitnessedSnakeConnecting R W F G U H
    p1 p1_epic middle p1_test q2 q2_monic q2_test))
  : τ (@CommRingPresentationMorphismAgreement R G U
      (@comm_ring_presentation_morphism_map R G U
        (@comm_ring_presentation_morphism_comp R G H U q2
          (@comm_ring_freyd_witnessed_snake_connecting_raw R W F G U H
            p1 p1_epic middle p1_test q2 q2_monic q2_test S)))
      (@comm_ring_presentation_morphism_map R G U
        (@comm_ring_freyd_witnessed_snake_u_raw R W F G U H
          p1 p1_epic middle p1_test q2 q2_monic q2_test S)))
≔ sigma_Snd (sigma_Snd (sigma_Snd S));
