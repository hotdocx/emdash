/*
  Witness-enriched formal colifts along Freyd epimorphisms.

  An epimorphism witness is the explicit agreement making the selected
  cokernel projection zero. Its block identity constructs a first
  weak-pullback cone. A test agreement annihilating the selected kernel,
  composed with the cone's selected factor, supplies the colift relation
  witness. This implements the relation-preserving raw/quotient colift of
  Posur Construction 3.15 without path decoding or runtime rules.

  Quotient reconstruction is constructed from a second cone over the same
  first weak pullback. Raw-competitor uniqueness is supplied by the downstream
  completion layer.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_normal_monomorphisms;

symbol CommRingFreydEpimorphismWitness
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R Q
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_presentation_morphism_map R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_freyd_cokernel_projection_raw R P Q f))
    (@comm_ring_presentation_morphism_map R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_zero R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f)));

symbol comm_ring_freyd_epimorphism_witness
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@nat_add
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_generators R Q))
≔ @comm_ring_presentation_agreement_witness R Q
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_presentation_morphism_map R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_freyd_cokernel_projection_raw R P Q f))
    (@comm_ring_presentation_morphism_map R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_presentation_morphism_zero R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f))) e;

symbol comm_ring_freyd_epimorphism_target_component
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R Q))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R Q)
    (@nat_add
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_matrix_proj1 R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_freyd_epimorphism_witness R P Q f e);

symbol comm_ring_freyd_epimorphism_source_component
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R P)
    (@nat_add
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_matrix_proj2 R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_freyd_epimorphism_witness R P Q f e);

// R_Q o sigma_RQ + F o sigma_A = id_B.
symbol comm_ring_freyd_epimorphism_block_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R Q))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_epimorphism_target_component R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R Q)))
≔ @eq_trans _ _
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@nat_add
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_matrix R
        (@comm_ring_freyd_cokernel_presentation R P Q f))
      (@comm_ring_matrix_vertical R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_freyd_epimorphism_target_component R P Q f e)
        (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R Q))
    (@eq_sym _ _ _
      (@comm_ring_matrix_horizontal_vertical_comp_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_epimorphism_target_component R P Q f e)
        (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
    (@eq_trans _ _
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_cokernel_presentation R P Q f))
        (@comm_ring_freyd_epimorphism_witness R P Q f e))
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R Q))
      (@eq_ap _ _
        (λ H : τ (@CommRingMatrix R
            (@nat_add
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R P))
            (@comm_ring_presentation_generators R Q)),
          @comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@nat_add
              (@comm_ring_presentation_relations R Q)
              (@comm_ring_presentation_generators R P))
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_matrix R
              (@comm_ring_freyd_cokernel_presentation R P Q f)) H)
        _ _
        (@comm_ring_matrix_vertical_proj_eta_path R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_freyd_epimorphism_witness R P Q f e)))
      (@eq_trans _ _
        (@comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R Q
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_freyd_cokernel_projection_raw R P Q f))
          (@comm_ring_presentation_morphism_map R Q
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_zero R Q
              (@comm_ring_freyd_cokernel_presentation R P Q f))))
        (@comm_ring_finite_free_id_matrix R
          (@comm_ring_presentation_generators R Q))
        (@comm_ring_presentation_agreement_law R Q
          (@comm_ring_freyd_cokernel_presentation R P Q f)
          (@comm_ring_presentation_morphism_map R Q
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_freyd_cokernel_projection_raw R P Q f))
          (@comm_ring_presentation_morphism_map R Q
            (@comm_ring_freyd_cokernel_presentation R P Q f)
            (@comm_ring_presentation_morphism_zero R Q
              (@comm_ring_freyd_cokernel_presentation R P Q f))) e)
        (@comm_ring_freyd_cokernel_sub_zero_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_finite_free_id_matrix R
            (@comm_ring_presentation_generators R Q)))));

symbol comm_ring_freyd_normal_epi_source_after_target_relations
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R Q))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_freyd_epimorphism_source_component R P Q f e)
    (@comm_ring_presentation_matrix R Q);

symbol comm_ring_freyd_normal_epi_target_after_target_relations
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R Q))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_freyd_epimorphism_target_component R P Q f e)
    (@comm_ring_presentation_matrix R Q);

symbol comm_ring_freyd_normal_epi_weak_pullback_right
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R Q))
≔ @comm_ring_matrix_sub R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_relations R Q))
    (@comm_ring_freyd_normal_epi_target_after_target_relations R P Q f e);

symbol comm_ring_freyd_epimorphism_block_after_relations_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_matrix_add R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_epimorphism_target_component R P Q f e))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
        (@comm_ring_presentation_matrix R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_finite_free_id_matrix R
          (@comm_ring_presentation_generators R Q))
        (@comm_ring_presentation_matrix R Q)))
≔ @eq_ap
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R Q))
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
    (λ z : τ (@CommRingMatrix R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)),
      @comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q) z
        (@comm_ring_presentation_matrix R Q))
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_epimorphism_target_component R P Q f e))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R Q))
    (@comm_ring_freyd_epimorphism_block_path R P Q f e);

symbol comm_ring_freyd_normal_epi_sum_to_composite_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_target_relations R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_matrix_add R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_epimorphism_target_component R P Q f e))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_epimorphism_source_component R P Q f e)))
        (@comm_ring_presentation_matrix R Q)))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_add_congr_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      _ _ _ _
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_epimorphism_target_component R P Q f e)
        (@comm_ring_presentation_matrix R Q))
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_epimorphism_source_component R P Q f e)
        (@comm_ring_presentation_matrix R Q)))
    (@eq_sym _ _ _
      (@comm_ring_matrix_comp_add_left_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_epimorphism_target_component R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_epimorphism_source_component R P Q f e))
        (@comm_ring_presentation_matrix R Q)));

symbol comm_ring_freyd_normal_epi_relation_sum_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_target_relations R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e)))
      (@comm_ring_presentation_matrix R Q))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_normal_epi_sum_to_composite_path R P Q f e)
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_epimorphism_block_after_relations_path R P Q f e)
      (@comm_ring_matrix_comp_left_identity_path R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)));

symbol comm_ring_freyd_normal_epi_right_action_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_weak_pullback_right R P Q f e))
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_target_relations
            R P Q f e))))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_sub_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_freyd_normal_epi_target_after_target_relations R P Q f e))
    (@eq_ap _ _
      (λ z : τ (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)),
        @comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q) z
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_normal_epi_target_after_target_relations
              R P Q f e)))
      _ _
      (@comm_ring_matrix_comp_right_identity_path R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)));

symbol comm_ring_freyd_normal_epi_compatibility_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_weak_pullback_right R P Q f e)))
≔ @eq_trans _ _ _ _
    (@abelian_group_add_eq_sub_left_path
      (Hom (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_finite_free_abelian_group_structure R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_target_after_target_relations R P Q f e))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e))
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_freyd_normal_epi_relation_sum_path R P Q f e))
    (@eq_sym _ _ _
      (@comm_ring_freyd_normal_epi_right_action_path R P Q f e));

symbol comm_ring_freyd_normal_epi_generic_compatibility_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_weak_pullback_right R P Q f e)))
≔ @eq_trans _ _ _ _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_epi_compatibility_path R P Q f e)
      (@eq_sym _ _ _
        (@comm_ring_finite_free_comp_fapp0_transparent_path R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_weak_pullback_right R P Q f e))));

symbol CommRingFreydNormalEpiTestAgreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R P T))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R
    (@comm_ring_freyd_kernel_presentation R W P Q f) T
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) T
      (@comm_ring_presentation_morphism_comp R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P T tau
        (@comm_ring_freyd_kernel_embedding_raw R W P Q f)))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) T
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_kernel_presentation R W P Q f) T));

symbol comm_ring_freyd_normal_epi_test_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R T)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
≔ @comm_ring_presentation_agreement_witness R
    (@comm_ring_freyd_kernel_presentation R W P Q f) T
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) T
      (@comm_ring_presentation_morphism_comp R
        (@comm_ring_freyd_kernel_presentation R W P Q f) P T tau
        (@comm_ring_freyd_kernel_embedding_raw R W P Q f)))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_kernel_presentation R W P Q f) T
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_kernel_presentation R W P Q f) T)) a;

symbol comm_ring_freyd_normal_epi_relation_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_relations R Q))
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e)
    (@comm_ring_freyd_normal_epi_weak_pullback_right R P Q f e)
    (@comm_ring_freyd_normal_epi_generic_compatibility_path R P Q f e);

symbol comm_ring_freyd_normal_epi_relation_factor
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R Q))
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
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_freyd_normal_epi_relation_cone R W P Q f e);

symbol comm_ring_freyd_normal_epi_colift_map
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  (tau : τ (@CommRingPresentationMorphism R P T))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R Q))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_morphism_map R P T tau)
    (@comm_ring_freyd_epimorphism_source_component R P Q f e);

symbol comm_ring_freyd_normal_epi_expected_relation_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_relations R Q))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R T)
    (@comm_ring_freyd_kernel_first_object R W P Q f)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a)
    (@comm_ring_freyd_normal_epi_relation_factor R W P Q f e);

symbol comm_ring_freyd_normal_epi_test_witness_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_kernel_first_object R W P Q f))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_morphism_map R P T tau)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)))
≔ @eq_trans _ _ _ _
    (@comm_ring_presentation_agreement_law R
      (@comm_ring_freyd_kernel_presentation R W P Q f) T
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_kernel_presentation R W P Q f) T
        (@comm_ring_presentation_morphism_comp R
          (@comm_ring_freyd_kernel_presentation R W P Q f) P T tau
          (@comm_ring_freyd_kernel_embedding_raw R W P Q f)))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_kernel_presentation R W P Q f) T
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_kernel_presentation R W P Q f) T)) a)
    (@comm_ring_freyd_cokernel_sub_zero_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_morphism_map R P T tau)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)));

symbol comm_ring_freyd_normal_epi_factor_proj1_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_normal_epi_relation_factor R W P Q f e))
      (@comm_ring_freyd_normal_epi_source_after_target_relations R P Q f e))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_normal_epi_relation_factor R W P Q f e)))
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
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_freyd_normal_epi_relation_cone R W P Q f e));

symbol comm_ring_freyd_normal_epi_colift_law
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_freyd_normal_epi_expected_relation_witness
          R W P Q T f e tau a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_freyd_normal_epi_colift_map R P Q T f e tau)
        (@comm_ring_presentation_matrix R Q)))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_assoc_path R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_matrix R T)
      (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a)
      (@comm_ring_freyd_normal_epi_relation_factor R W P Q f e))
    (@eq_trans _ _ _ _
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_freyd_kernel_first_object R W P Q f)),
          @comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_relations R Q) z
            (@comm_ring_freyd_normal_epi_relation_factor R W P Q f e))
        _ _
        (@comm_ring_freyd_normal_epi_test_witness_path R W P Q T f tau a))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comm_ring_matrix_comp_assoc_path R
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R P T tau)
            (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
            (@comm_ring_freyd_normal_epi_relation_factor R W P Q f e)))
        (@eq_trans _ _ _ _
          (@eq_ap _ _
            (λ z : τ (@CommRingMatrix R
                (@comm_ring_presentation_generators R P)
                (@comm_ring_presentation_relations R Q)),
              @comm_ring_matrix_comp R
                (@comm_ring_presentation_generators R T)
                (@comm_ring_presentation_generators R P)
                (@comm_ring_presentation_relations R Q)
                (@comm_ring_presentation_morphism_map R P T tau) z)
            _ _
            (@comm_ring_freyd_normal_epi_factor_proj1_path R W P Q f e))
          (@comm_ring_matrix_comp_assoc_path R
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R P T tau)
            (@comm_ring_freyd_epimorphism_source_component R P Q f e)
            (@comm_ring_presentation_matrix R Q)))));

symbol comm_ring_freyd_normal_epi_colift_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@CommRingPresentationMorphism R Q T)
≔ @comm_ring_presentation_morphism_intro R Q T
    (@comm_ring_freyd_normal_epi_colift_map R P Q T f e tau)
    (@comm_ring_freyd_normal_epi_expected_relation_witness
      R W P Q T f e tau a)
    (@comm_ring_freyd_normal_epi_colift_law R W P Q T f e tau a);

symbol comm_ring_freyd_normal_epi_colift
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@CommRingFreydHomSet R Q T)
≔ @comm_ring_freyd_hom_class R Q T
    (@comm_ring_freyd_normal_epi_colift_raw R W P Q T f e tau a);

// Components of the reconstruction cone over the source generators.
symbol comm_ring_freyd_normal_epi_source_after_source_map
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_freyd_epimorphism_source_component R P Q f e)
    (@comm_ring_presentation_morphism_map R P Q f);

symbol comm_ring_freyd_normal_epi_target_after_source_map
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_freyd_epimorphism_target_component R P Q f e)
    (@comm_ring_presentation_morphism_map R P Q f);

symbol comm_ring_freyd_normal_epi_reconstruction_left
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_sub R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R P))
    (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e);

// (R_Q sigma_RQ + F sigma_A) F = F.
symbol comm_ring_freyd_epimorphism_block_after_source_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e)))
      (@comm_ring_presentation_morphism_map R P Q f))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_add_congr_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      _ _ _ _
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_epimorphism_target_component R P Q f e)
        (@comm_ring_presentation_morphism_map R P Q f))
      (@comm_ring_matrix_comp_assoc_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_epimorphism_source_component R P Q f e)
        (@comm_ring_presentation_morphism_map R P Q f)))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@comm_ring_matrix_comp_add_left_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_freyd_epimorphism_target_component R P Q f e))
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_epimorphism_source_component R P Q f e))
          (@comm_ring_presentation_morphism_map R P Q f)))
      (@eq_trans _ _ _ _
        (@eq_ap _ _
          (λ z : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R Q)),
            @comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R Q)
              (@comm_ring_presentation_generators R P) z
              (@comm_ring_presentation_morphism_map R P Q f))
          _ _ (@comm_ring_freyd_epimorphism_block_path R P Q f e))
        (@comm_ring_matrix_comp_left_identity_path R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R P Q f))));

symbol comm_ring_freyd_epimorphism_block_after_source_commuted_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e)))
      (@comm_ring_presentation_morphism_map R P Q f))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_add_comm_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e)))
    (@comm_ring_freyd_epimorphism_block_after_source_path R P Q f e);

symbol comm_ring_freyd_normal_epi_reconstruction_left_action_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e))
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_sub_right_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R P))
      (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))
    (@eq_ap _ _
      (λ z : τ (@CommRingMatrix R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)),
        @comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P) z
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_morphism_map R P Q f)
            (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e)))
      _ _
      (@comm_ring_matrix_comp_right_identity_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)));

symbol comm_ring_freyd_normal_epi_reconstruction_compatibility_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e)))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_normal_epi_reconstruction_left_action_path R P Q f e)
    (@eq_sym _ _ _
      (@abelian_group_add_eq_sub_left_path
        (Hom (@CommRingFiniteFree_cat R)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q))
        (@comm_ring_finite_free_abelian_group_structure R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e))
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_epimorphism_block_after_source_commuted_path
          R P Q f e)));

symbol comm_ring_freyd_normal_epi_reconstruction_generic_compatibility_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e)))
≔ @eq_trans _ _ _ _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_normal_epi_reconstruction_compatibility_path
        R P Q f e)
      (@eq_sym _ _ _
        (@comm_ring_finite_free_comp_fapp0_transparent_path R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e))));

symbol comm_ring_freyd_normal_epi_reconstruction_cone
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@WeakPullbackCone
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_generators R P))
≔ @weak_pullback_cone_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e)
    (@comm_ring_freyd_normal_epi_target_after_source_map R P Q f e)
    (@comm_ring_freyd_normal_epi_reconstruction_generic_compatibility_path
      R P Q f e);

symbol comm_ring_freyd_normal_epi_reconstruction_factor
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@CommRingMatrix R
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R P))
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
    (@comm_ring_presentation_generators R P)
    (@comm_ring_freyd_normal_epi_reconstruction_cone R W P Q f e);

symbol comm_ring_freyd_normal_epi_reconstruction_factor_proj1_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e))
      (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
        (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e)))
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
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_normal_epi_reconstruction_cone R W P Q f e));

symbol comm_ring_freyd_normal_epi_reconstruction_factor_action_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_relations R T)
          (@comm_ring_freyd_kernel_first_object R W P Q f)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a)
          (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P T tau)
        (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e)))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_assoc_path R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_matrix R T)
      (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a)
      (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e))
    (@eq_trans _ _ _ _
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_freyd_kernel_first_object R W P Q f)),
          @comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_generators R P) z
            (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e))
        _ _
        (@comm_ring_freyd_normal_epi_test_witness_path R W P Q T f tau a))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _
          (@comm_ring_matrix_comp_assoc_path R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_kernel_first_object R W P Q f)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_morphism_map R P T tau)
            (@comm_ring_freyd_kernel_first_proj1 R W P Q f)
            (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e)))
        (@eq_ap _ _
          (λ z : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_generators R P)),
            @comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R T)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_morphism_map R P T tau) z)
          _ _
          (@comm_ring_freyd_normal_epi_reconstruction_factor_proj1_path
            R W P Q f e))));

symbol comm_ring_freyd_normal_epi_tau_reconstruction_left_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  (tau : τ (@CommRingPresentationMorphism R P T))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P T tau)
        (@comm_ring_freyd_normal_epi_reconstruction_left R P Q f e))
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P T tau)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R P T tau)
          (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_sub_right_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_morphism_map R P T tau)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R P))
      (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))
    (@eq_ap _ _
      (λ z : τ (@CommRingMatrix R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R P)),
        @comm_ring_matrix_sub R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R P) z
          (@comm_ring_matrix_comp R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_morphism_map R P T tau)
            (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e)))
      _ _
      (@comm_ring_matrix_comp_right_identity_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_morphism_map R P T tau)));

symbol comm_ring_freyd_normal_epi_tau_source_assoc_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  (tau : τ (@CommRingPresentationMorphism R P T))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P T tau)
        (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_normal_epi_colift_map R P Q T f e tau)
        (@comm_ring_presentation_morphism_map R P Q f)))
≔ @comm_ring_matrix_comp_assoc_path R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R T)
    (@comm_ring_presentation_morphism_map R P T tau)
    (@comm_ring_freyd_epimorphism_source_component R P Q f e)
    (@comm_ring_presentation_morphism_map R P Q f);

symbol comm_ring_freyd_normal_epi_reconstruction_witness
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_neg R
    (@comm_ring_presentation_relations R T)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_relations R T)
      (@comm_ring_freyd_kernel_first_object R W P Q f)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a)
      (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e));

symbol comm_ring_freyd_normal_epi_reconstruction_witness_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_freyd_normal_epi_reconstruction_witness
          R W P Q T f e tau a))
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_freyd_normal_epi_colift_map R P Q T f e tau)
          (@comm_ring_presentation_morphism_map R P Q f))
        (@comm_ring_presentation_morphism_map R P T tau)))
≔ @eq_trans _ _ _ _
    (@comm_ring_matrix_comp_neg_right_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R T)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_relations R T)
        (@comm_ring_freyd_kernel_first_object R W P Q f)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_freyd_normal_epi_test_witness R W P Q T f tau a)
        (@comm_ring_freyd_normal_epi_reconstruction_factor R W P Q f e)))
    (@eq_trans _ _ _ _
      (@eq_ap _ _
        (λ z : τ (@CommRingMatrix R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R P)),
          @comm_ring_matrix_neg R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R P) z)
        _ _
        (@comm_ring_freyd_normal_epi_reconstruction_factor_action_path
          R W P Q T f e tau a))
      (@eq_trans _ _ _ _
        (@eq_ap _ _
          (λ z : τ (@CommRingMatrix R
              (@comm_ring_presentation_generators R T)
              (@comm_ring_presentation_generators R P)),
            @comm_ring_matrix_neg R
              (@comm_ring_presentation_generators R T)
              (@comm_ring_presentation_generators R P) z)
          _ _
          (@comm_ring_freyd_normal_epi_tau_reconstruction_left_path
            R P Q T f e tau))
        (@eq_trans _ _ _ _
          (@comm_ring_matrix_neg_sub_swap_path R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_morphism_map R P T tau)
            (@comm_ring_matrix_comp R
              (@comm_ring_presentation_generators R T)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_generators R P)
              (@comm_ring_presentation_morphism_map R P T tau)
              (@comm_ring_freyd_normal_epi_source_after_source_map R P Q f e)))
          (@eq_ap _ _
            (λ z : τ (@CommRingMatrix R
                (@comm_ring_presentation_generators R T)
                (@comm_ring_presentation_generators R P)),
              @comm_ring_matrix_sub R
                (@comm_ring_presentation_generators R T)
                (@comm_ring_presentation_generators R P) z
                (@comm_ring_presentation_morphism_map R P T tau))
            _ _
            (@comm_ring_freyd_normal_epi_tau_source_assoc_path
              R P Q T f e tau)))));

symbol comm_ring_freyd_normal_epi_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@CommRingPresentationMorphismAgreement R P T
      (@comm_ring_presentation_morphism_map R P T
        (@comm_ring_presentation_morphism_comp R P Q T
          (@comm_ring_freyd_normal_epi_colift_raw R W P Q T f e tau a) f))
      (@comm_ring_presentation_morphism_map R P T tau))
≔ @comm_ring_presentation_morphism_agreement_intro R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T
        (@comm_ring_freyd_normal_epi_colift_raw R W P Q T f e tau a) f))
    (@comm_ring_presentation_morphism_map R P T tau)
    (@comm_ring_freyd_normal_epi_reconstruction_witness
      R W P Q T f e tau a)
    (@comm_ring_freyd_normal_epi_reconstruction_witness_path
      R W P Q T f e tau a);

symbol comm_ring_freyd_normal_epi_reconstruction_path
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P Q T : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R P Q)]
  (e : τ (@CommRingFreydEpimorphismWitness R P Q f))
  [tau : τ (@CommRingPresentationMorphism R P T)]
  (a : τ (@CommRingFreydNormalEpiTestAgreement R W P Q T f tau))
  : τ (@= (@CommRingFreydHomSet R P T)
      (@comm_ring_freyd_comp R P Q T
        (@comm_ring_freyd_normal_epi_colift R W P Q T f e tau a)
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_hom_class R P T tau))
≔ @comm_ring_freyd_agreement_path R P T
    (@comm_ring_presentation_morphism_comp R P Q T
      (@comm_ring_freyd_normal_epi_colift_raw R W P Q T f e tau a) f)
    tau
    (@comm_ring_freyd_normal_epi_reconstruction_agreement
      R W P Q T f e tau a);
