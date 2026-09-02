/*
  Witness-enriched formal lifts along Freyd monomorphisms.

  A monomorphism witness is the explicit agreement making the selected kernel
  embedding zero. A test agreement against the formal cokernel splits into
  target-relation and source-generator components. Matrix and abelian-group
  laws construct the first-weak-pullback cone; its selected factor and the
  monomorphism witness construct the lift's relation witness. The resulting
  raw/quotient lift, reconstruction agreement, and raw-competitor uniqueness
  implement Posur Construction 3.14 without decoding arbitrary truncated
  paths or adding runtime rules.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_witnessed_preabelian;
require open emdash.emdash3_2_abelian_categories;

symbol abelian_group_add_eq_sub_right_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a b c : τ A)
  (p : τ (@= A
    (@abelian_group_ops_add A (@abelian_group_structure_ops A S) a b) c))
  : τ (@= A
      (@abelian_group_ops_add A (@abelian_group_structure_ops A S) b
        (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) c))
      (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) a))
≔ @abelian_group_add_inverse_unique_path A S a
    (@abelian_group_ops_add A (@abelian_group_structure_ops A S) b
      (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) c))
    (@eq_trans A _ _ _
      (@eq_sym A _ _
        (@abelian_group_add_assoc_law A S a b
          (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) c)))
      (@eq_trans A _ _ _
        (@eq_ap A A
          (λ z : τ A,
            @abelian_group_ops_add A (@abelian_group_structure_ops A S) z
              (@abelian_group_ops_neg A (@abelian_group_structure_ops A S) c))
          _ _ p)
        ((@abelian_group_add_inv_law A S) c)));
symbol CommRingFreydMonomorphismWitness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R
    (@comm_ring_freyd_kernel_presentation R W P Q f) P
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P
      (@comm_ring_freyd_kernel_embedding_raw R W P Q f))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P));

symbol comm_ring_freyd_monomorphism_sigma
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
≔ @comm_ring_presentation_agreement_witness R
    (@comm_ring_freyd_kernel_presentation R W P Q f) P
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P
      (@comm_ring_freyd_kernel_embedding_raw R W P Q f))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P))
    m;

symbol CommRingFreydNormalMonoTestAgreement
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R T
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_presentation_morphism_map R T
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_comp R T Q
        (@comm_ring_freyd_cokernel_presentation R P Q f)
        (@comm_ring_freyd_cokernel_projection_raw R P Q f) tau))
    (@comm_ring_presentation_morphism_map R T
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_zero R T
        (@comm_ring_freyd_cokernel_presentation R P Q f)));

symbol comm_ring_freyd_normal_mono_test_witness
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@nat_add
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_presentation_agreement_witness R T
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_presentation_morphism_map R T
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_comp R T Q
        (@comm_ring_freyd_cokernel_presentation R P Q f)
        (@comm_ring_freyd_cokernel_projection_raw R P Q f) tau))
    (@comm_ring_presentation_morphism_map R T
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_zero R T
        (@comm_ring_freyd_cokernel_presentation R P Q f)))
    a;

symbol comm_ring_freyd_normal_mono_target_component
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R Q)
    (@nat_add
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_presentation_generators R T)
    (@comm_ring_matrix_proj1 R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_freyd_normal_mono_test_witness R P Q T f tau a);

symbol comm_ring_freyd_normal_mono_lift_map
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R P)
    (@nat_add
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_presentation_generators R T)
    (@comm_ring_matrix_proj2 R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_freyd_normal_mono_test_witness R P Q T f tau a);

// R_Q o tau_RQ + F o tau_A = tau.
symbol comm_ring_freyd_normal_mono_block_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
      (@comm_ring_presentation_morphism_map R T Q tau))
≔ @eq_trans _ _
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@nat_add
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_matrix R
        (@comm_ring_freyd_cokernel_presentation R P Q f))
      (@comm_ring_matrix_vertical R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a)
        (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
    (@comm_ring_presentation_morphism_map R T Q tau)
    (@eq_sym _ _ _
      (@comm_ring_matrix_horizontal_vertical_comp_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a)
        (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
    (@eq_trans _ _
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_cokernel_presentation R P Q f))
        (@comm_ring_freyd_normal_mono_test_witness R P Q T f tau a))
      (@comm_ring_presentation_morphism_map R T Q tau)
      (@eq_ap _ _
        (λ H : τ (@CommRingMatrix R
            (@nat_add
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R P))
            (@comm_ring_presentation_generators R T)),
          @comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@nat_add
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R P))
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_matrix R
              (@comm_ring_freyd_cokernel_presentation R P Q f)) H)
        _ _
        (@comm_ring_matrix_vertical_proj_eta_path R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_freyd_normal_mono_test_witness R P Q T f tau a)))
      (@eq_trans _ _
        (@comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R T
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_comp R T Q
              (@comm_ring_freyd_cokernel_presentation R P Q f)
              (@comm_ring_freyd_cokernel_projection_raw R P Q f) tau))
          (@comm_ring_presentation_morphism_map R T
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_zero R T
              (@comm_ring_freyd_cokernel_presentation R P Q f))))
        (@comm_ring_presentation_morphism_map R T Q tau)
        (@comm_ring_presentation_agreement_law R T
          (@comm_ring_freyd_cokernel_presentation R P Q f)
          (@comm_ring_presentation_morphism_map R T
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_comp R T Q
              (@comm_ring_freyd_cokernel_presentation R P Q f)
              (@comm_ring_freyd_cokernel_projection_raw R P Q f) tau))
          (@comm_ring_presentation_morphism_map R T
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_zero R T
              (@comm_ring_freyd_cokernel_presentation R P Q f)))
          a)
        (@eq_trans _ _
          (@comm_ring_presentation_morphism_map R T
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_comp R T Q
              (@comm_ring_freyd_cokernel_presentation R P Q f)
              (@comm_ring_freyd_cokernel_projection_raw R P Q f) tau))
          (@comm_ring_presentation_morphism_map R T Q tau)
          (@comm_ring_freyd_cokernel_sub_zero_path R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R T
              (@comm_ring_freyd_cokernel_presentation R P Q f)
              (@comm_ring_presentation_morphism_comp R T Q
                (@comm_ring_freyd_cokernel_presentation R P Q f)
                (@comm_ring_freyd_cokernel_projection_raw R P Q f) tau)))
          (@comm_ring_matrix_comp_left_identity_path R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_morphism_map R T Q tau)))));

symbol comm_ring_freyd_normal_mono_lift_after_relations
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)
    (@comm_ring_presentation_matrix R T);

symbol comm_ring_freyd_normal_mono_target_after_relations
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a)
    (@comm_ring_presentation_matrix R T);

symbol comm_ring_freyd_normal_mono_weak_pullback_right
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_matrix_sub R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_presentation_morphism_witness R T Q tau)
    (@comm_ring_freyd_normal_mono_target_after_relations R P Q T f tau a);

symbol comm_ring_freyd_normal_mono_block_after_relations_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_add R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
        (@comm_ring_presentation_matrix R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_morphism_map R T Q tau)
        (@comm_ring_presentation_matrix R T)))
≔ @eq_ap
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
    (λ z : τ (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)),
      @comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T) z
        (@comm_ring_presentation_matrix R T))
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
    (@comm_ring_presentation_morphism_map R T Q tau)
    (@comm_ring_freyd_normal_mono_block_path R P Q T f tau a);

symbol comm_ring_freyd_normal_mono_tau_relations_path
  [R : τ CommRing]
  [T Q : τ (@CommRingPresentation R)]
  (tau : τ (@CommRingPresentationMorphism R T Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_morphism_map R T Q tau)
        (@comm_ring_presentation_matrix R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R T Q tau)))
≔ @eq_sym _ _ _ (@comm_ring_presentation_morphism_law R T Q tau);

symbol comm_ring_freyd_normal_mono_sum_to_composite_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_target_after_relations
            R P Q T f tau a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R T)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_mono_lift_after_relations
            R P Q T f tau a)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_add R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)))
        (@comm_ring_presentation_matrix R T)))
≔ @eq_trans _ _
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
        (@comm_ring_presentation_matrix R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a))
        (@comm_ring_presentation_matrix R T)))
    _
    (@comm_ring_matrix_add_congr_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T)
      _ _ _ _
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a)
        (@comm_ring_presentation_matrix R T))
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)
        (@comm_ring_presentation_matrix R T)))
    (@eq_sym _ _ _
      (@comm_ring_matrix_comp_add_left_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a))
        (@comm_ring_presentation_matrix R T)));


symbol comm_ring_freyd_normal_mono_relation_sum_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_target_after_relations
            R P Q T f tau a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R T)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_mono_lift_after_relations
            R P Q T f tau a)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R T Q tau)))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_normal_mono_sum_to_composite_path R P Q T f tau a)
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_mono_block_after_relations_path
        R P Q T f tau a)
      (@comm_ring_freyd_normal_mono_tau_relations_path R T Q tau));

symbol comm_ring_freyd_normal_mono_compatibility_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_lift_after_relations R P Q T f tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_weak_pullback_right R P Q T f tau a)))
≔ @eq_trans _ _
    (@comm_ring_matrix_sub R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R T Q tau))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_target_after_relations R P Q T f tau a)))
    _
    (@abelian_group_add_eq_sub_left_path
      (Hom (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_finite_free_abelian_group_structure R
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_target_after_relations R P Q T f tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_lift_after_relations R P Q T f tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R T Q tau))
      (@comm_ring_freyd_normal_mono_relation_sum_path R P Q T f tau a))
    (@eq_sym _ _ _
      (@comm_ring_matrix_comp_sub_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R T Q tau)
        (@comm_ring_freyd_normal_mono_target_after_relations R P Q T f tau a)));

symbol comm_ring_freyd_normal_mono_generic_compatibility_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_lift_after_relations R P Q T f tau a))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_weak_pullback_right R P Q T f tau a)))
≔ @eq_trans _ _ _ _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_freyd_normal_mono_lift_after_relations R P Q T f tau a))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_mono_compatibility_path R P Q T f tau a)
      (@eq_sym _ _ _
        (@comm_ring_finite_free_comp_fapp0_transparent_path R
          (@comm_ring_presentation_relations R T)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_weak_pullback_right R P Q T f tau a))));

symbol comm_ring_freyd_normal_mono_relation_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_relations R T))
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_normal_mono_lift_after_relations R P Q T f tau a)
    (@comm_ring_freyd_normal_mono_weak_pullback_right R P Q T f tau a)
    (@comm_ring_freyd_normal_mono_generic_compatibility_path
      R P Q T f tau a);

symbol comm_ring_freyd_normal_mono_relation_factor
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T Q))
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R T))
≔ @computational_weak_pullback_lift
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_normal_mono_relation_cone R W P Q T f tau a);

symbol comm_ring_freyd_monomorphism_sigma_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_freyd_monomorphism_sigma R W P Q f m))
      (@comm_ring_freyd_kernel_first_proj1 R W P Q f))
≔ @eq_trans _ _ _ _
    (@comm_ring_presentation_agreement_law R
      (@comm_ring_freyd_kernel_presentation R W P Q f) P
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P
        (@comm_ring_freyd_kernel_embedding_raw R W P Q f))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_kernel_presentation R W P Q f) P))
      m)
    (@comm_ring_freyd_cokernel_sub_zero_path R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_freyd_kernel_first_proj1 R W P Q f));

symbol comm_ring_freyd_normal_mono_expected_relation_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R T))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_monomorphism_sigma R W P Q f m)
    (@comm_ring_freyd_normal_mono_relation_factor R W P Q T f tau a);

symbol comm_ring_freyd_normal_mono_lift_law
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_freyd_normal_mono_expected_relation_witness
          R W P Q T f m tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)
        (@comm_ring_presentation_matrix R T)))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_assoc_path R
      (@comm_ring_presentation_relations R T)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_freyd_monomorphism_sigma R W P Q f m)
      (@comm_ring_freyd_normal_mono_relation_factor R W P Q T f tau a))
    (@eq_trans _ _ _ _
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_kernel_first_object R W P Q f)),
          @comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_relations R T) z
            (@comm_ring_freyd_normal_mono_relation_factor R W P Q T f tau a))
        _ _ (@comm_ring_freyd_monomorphism_sigma_path R W P Q f m))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comm_ring_finite_free_comp_fapp0_transparent_path R
            (@comm_ring_presentation_relations R T)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
            (@comm_ring_freyd_normal_mono_relation_factor R W P Q T f tau a)))
        (@computational_weak_pullback_lift_proj1_path
          (@CommRingFiniteFree_cat R)
          (@comm_ring_finite_free_direct_sum_func R)
          zero (@comm_ring_finite_free_additive R)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f)
          (@comm_ring_presentation_relations R T)
          (@comm_ring_freyd_normal_mono_relation_cone R W P Q T f tau a))));

symbol comm_ring_freyd_normal_mono_lift_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingPresentationMorphism R T P)
≔ @comm_ring_presentation_morphism_intro R T P
    (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a)
    (@comm_ring_freyd_normal_mono_expected_relation_witness
      R W P Q T f m tau a)
    (@comm_ring_freyd_normal_mono_lift_law R W P Q T f m tau a);

symbol comm_ring_freyd_normal_mono_lift
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingFreydHomSet R T P)
≔ @comm_ring_freyd_hom_class R T P
    (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a);

symbol comm_ring_freyd_normal_mono_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@CommRingPresentationMorphismAgreement R T Q
      (@comm_ring_presentation_morphism_map R T Q
        (@comm_ring_presentation_morphism_comp R T P Q f
          (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)))
      (@comm_ring_presentation_morphism_map R T Q tau))
≔ @comm_ring_presentation_morphism_agreement_intro R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f
        (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)))
    (@comm_ring_presentation_morphism_map R T Q tau)
    (@comm_ring_matrix_neg R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
    (@eq_trans _ _ _ _
      (@comm_ring_matrix_comp_neg_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
      (@eq_sym _ _ _
        (@abelian_group_add_eq_sub_right_path
          (Hom (@CommRingFiniteFree_cat R)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R Q))
          (@comm_ring_finite_free_abelian_group_structure R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R Q))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_normal_mono_target_component R P Q T f tau a))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a))
          (@comm_ring_presentation_morphism_map R T Q tau)
          (@comm_ring_freyd_normal_mono_block_path R P Q T f tau a))));

symbol comm_ring_freyd_normal_mono_reconstruction_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  : τ (@= (@CommRingFreydHomSet R T Q)
      (@comm_ring_freyd_comp R T P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_normal_mono_lift R W P Q T f m tau a))
      (@comm_ring_freyd_hom_class R T Q tau))
≔ @comm_ring_freyd_agreement_path R T Q
    (@comm_ring_presentation_morphism_comp R T P Q f
      (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a))
    tau
    (@comm_ring_freyd_normal_mono_reconstruction_agreement
      R W P Q T f m tau a);

// A competing raw lift reconstructing tau determines a cone for the
// difference from the selected lift.
symbol comm_ring_freyd_normal_mono_competing_composite_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@CommRingPresentationMorphismAgreement R T Q
      (@comm_ring_presentation_morphism_map R T Q
        (@comm_ring_presentation_morphism_comp R T P Q f k))
      (@comm_ring_presentation_morphism_map R T Q
        (@comm_ring_presentation_morphism_comp R T P Q f
          (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a))))
≔ @comm_ring_presentation_agreement_trans R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f
        (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)))
    reconstructs
    (@comm_ring_presentation_agreement_sym R T Q
      (@comm_ring_presentation_morphism_map R T Q
        (@comm_ring_presentation_morphism_comp R T P Q f
          (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)))
      (@comm_ring_presentation_morphism_map R T Q tau)
      (@comm_ring_freyd_normal_mono_reconstruction_agreement
        R W P Q T f m tau a));

symbol comm_ring_freyd_normal_mono_competing_difference
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_matrix_sub R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_morphism_map R T P k)
    (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a);

symbol comm_ring_freyd_normal_mono_competing_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_presentation_agreement_witness R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f
        (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)))
    (@comm_ring_freyd_normal_mono_competing_composite_agreement
      R W P Q T f m tau a k reconstructs);

symbol comm_ring_freyd_normal_mono_competing_compatibility_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_competing_difference
          R W P Q T f m tau a k))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_competing_witness
          R W P Q T f m tau a k reconstructs)))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_sub_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R T P k)
      (@comm_ring_freyd_normal_mono_lift_map R P Q T f tau a))
    (@eq_sym _ _ _
      (@comm_ring_presentation_agreement_law R T Q
        (@comm_ring_presentation_morphism_map R T Q
          (@comm_ring_presentation_morphism_comp R T P Q f k))
        (@comm_ring_presentation_morphism_map R T Q
          (@comm_ring_presentation_morphism_comp R T P Q f
            (@comm_ring_freyd_normal_mono_lift_raw
              R W P Q T f m tau a)))
        (@comm_ring_freyd_normal_mono_competing_composite_agreement
          R W P Q T f m tau a k reconstructs)));

symbol comm_ring_freyd_normal_mono_competing_generic_compatibility_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_mono_competing_difference
          R W P Q T f m tau a k))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_mono_competing_witness
          R W P Q T f m tau a k reconstructs)))
≔ @eq_trans _ _ _ _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_freyd_normal_mono_competing_difference
        R W P Q T f m tau a k))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_mono_competing_compatibility_path
        R W P Q T f m tau a k reconstructs)
      (@eq_sym _ _ _
        (@comm_ring_finite_free_comp_fapp0_transparent_path R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_mono_competing_witness
            R W P Q T f m tau a k reconstructs))));

symbol comm_ring_freyd_normal_mono_competing_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_generators R T))
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_normal_mono_competing_difference
      R W P Q T f m tau a k)
    (@comm_ring_freyd_normal_mono_competing_witness
      R W P Q T f m tau a k reconstructs)
    (@comm_ring_freyd_normal_mono_competing_generic_compatibility_path
      R W P Q T f m tau a k reconstructs);

symbol comm_ring_freyd_normal_mono_competing_factor
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R T))
≔ @computational_weak_pullback_lift
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_freyd_normal_mono_competing_cone
      R W P Q T f m tau a k reconstructs);

symbol comm_ring_freyd_normal_mono_competing_factor_proj1_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_normal_mono_competing_factor
          R W P Q T f m tau a k reconstructs))
      (@comm_ring_freyd_normal_mono_competing_difference
        R W P Q T f m tau a k))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_normal_mono_competing_factor
          R W P Q T f m tau a k reconstructs)))
    (@computational_weak_pullback_lift_proj1_path
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_freyd_kernel_first_weak_pullback R W P Q f)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_normal_mono_competing_cone
        R W P Q T f m tau a k reconstructs));

symbol comm_ring_freyd_normal_mono_uniqueness_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_generators R T))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R P)
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_freyd_monomorphism_sigma R W P Q f m)
    (@comm_ring_freyd_normal_mono_competing_factor
      R W P Q T f m tau a k reconstructs);

symbol comm_ring_freyd_normal_mono_uniqueness_witness_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R T))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_freyd_normal_mono_uniqueness_witness
          R W P Q T f m tau a k reconstructs))
      (@comm_ring_freyd_normal_mono_competing_difference
        R W P Q T f m tau a k))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_assoc_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_freyd_monomorphism_sigma R W P Q f m)
      (@comm_ring_freyd_normal_mono_competing_factor
        R W P Q T f m tau a k reconstructs))
    (@eq_trans _ _ _ _
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_kernel_first_object R W P Q f)),
          @comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_generators R T) z
            (@comm_ring_freyd_normal_mono_competing_factor
              R W P Q T f m tau a k reconstructs))
        _ _ (@comm_ring_freyd_monomorphism_sigma_path R W P Q f m))
      (@comm_ring_freyd_normal_mono_competing_factor_proj1_path
        R W P Q T f m tau a k reconstructs));

symbol comm_ring_freyd_normal_mono_uniqueness_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@CommRingPresentationMorphismAgreement R T P
      (@comm_ring_presentation_morphism_map R T P k)
      (@comm_ring_presentation_morphism_map R T P
        (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)))
≔ @comm_ring_presentation_morphism_agreement_intro R T P
    (@comm_ring_presentation_morphism_map R T P k)
    (@comm_ring_presentation_morphism_map R T P
      (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a))
    (@comm_ring_freyd_normal_mono_uniqueness_witness
      R W P Q T f m tau a k reconstructs)
    (@comm_ring_freyd_normal_mono_uniqueness_witness_path
      R W P Q T f m tau a k reconstructs);

symbol comm_ring_freyd_normal_mono_uniqueness_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (m : τ (@CommRingFreydMonomorphismWitness R W P Q f))
  [tau : τ (@CommRingPresentationMorphism R T Q)]
  (a : τ (@CommRingFreydNormalMonoTestAgreement R P Q T f tau))
  (k : τ (@CommRingPresentationMorphism R T P))
  (reconstructs : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f k))
    (@comm_ring_presentation_morphism_map R T Q tau)))
  : τ (@= (@CommRingFreydHomSet R T P)
      (@comm_ring_freyd_hom_class R T P k)
      (@comm_ring_freyd_normal_mono_lift R W P Q T f m tau a))
≔ @comm_ring_freyd_agreement_path R T P k
    (@comm_ring_freyd_normal_mono_lift_raw R W P Q T f m tau a)
    (@comm_ring_freyd_normal_mono_uniqueness_agreement
      R W P Q T f m tau a k reconstructs);
