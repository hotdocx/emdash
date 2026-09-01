/*
  Witness-enriched formal Freyd cokernels.

  The target relations are enlarged by the morphism datum. The projection is
  ambient identity. An explicit agreement witnessing a zero composite supplies
  the second block of the induced colift's relation witness; quotient paths
  then prove annihilation, reconstruction, and uniqueness. No decoder from an
  arbitrary set-truncated equality back to raw agreement is postulated.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_additive;

symbol comm_ring_freyd_cokernel_presentation
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R
    (@comm_ring_presentation_generators R Q)
    (@nat_add
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_matrix_horizontal R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_map R P Q f));

// A - 0 = A for the matrix subtraction used by agreement.
symbol comm_ring_freyd_cokernel_sub_zero_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_sub R rows columns A
        (@comm_ring_matrix_zero R rows columns))
      A)
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    (@comm_ring_matrix_sub R rows columns A
      (@comm_ring_matrix_zero R rows columns))
    (@comm_ring_matrix_add R rows columns A
      (@comm_ring_matrix_zero R rows columns))
    A
    (@comm_ring_matrix_add_congr_path R rows columns
      A A
      (@comm_ring_matrix_neg R rows columns
        (@comm_ring_matrix_zero R rows columns))
      (@comm_ring_matrix_zero R rows columns)
      (@eq_refl (@CommRingMatrix R rows columns) A)
      (@comm_ring_matrix_neg_zero_path R rows columns))
    (@comm_ring_matrix_add_zero_right_path R rows columns A);

// [R_Q,F] o inl = R_Q.
symbol comm_ring_freyd_cokernel_inl_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_cokernel_presentation R P Q f))
        (@comm_ring_matrix_inl R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)))
      (@comm_ring_presentation_matrix R Q))
≔ @eq_trans
    _ _
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_finite_free_id_matrix R
          (@comm_ring_presentation_relations R Q)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_matrix_zero R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R Q))))
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_matrix_horizontal_vertical_comp_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R Q)))
    (@eq_trans
      _ _
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_matrix_zero R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)))
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_matrix_add_congr_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        _ _ _ _
        (@comm_ring_matrix_comp_right_identity_path R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_matrix R Q))
        (@comm_ring_matrix_comp_zero_right_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R P Q f)))
      (@comm_ring_matrix_add_zero_right_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R Q)));

// [R_Q,F] o inr = F.
symbol comm_ring_freyd_cokernel_inr_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_cokernel_presentation R P Q f))
        (@comm_ring_matrix_inr R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)))
      (@comm_ring_presentation_morphism_map R P Q f))
≔ @eq_trans
    _ _
    (@comm_ring_matrix_add R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_matrix_zero R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_finite_free_id_matrix R
          (@comm_ring_presentation_generators R P))))
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_matrix_horizontal_vertical_comp_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_matrix_zero R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P))
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R P)))
    (@eq_trans
      _ _
      (@comm_ring_matrix_add R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_matrix_zero R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_morphism_map R P Q f))
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_matrix_add_congr_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        _ _ _ _
        (@comm_ring_matrix_comp_zero_right_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_matrix R Q))
        (@comm_ring_matrix_comp_right_identity_path R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R P Q f)))
      (@comm_ring_matrix_add_zero_left_path R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P Q f)));

symbol comm_ring_freyd_cokernel_projection_law
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_cokernel_presentation R P Q f))
        (@comm_ring_matrix_inl R
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_finite_free_id_matrix R
          (@comm_ring_presentation_generators R Q))
        (@comm_ring_presentation_matrix R Q)))
≔ @eq_trans _ _
    (@comm_ring_presentation_matrix R Q) _
    (@comm_ring_freyd_cokernel_inl_path R P Q f)
    (@eq_sym _ _ _
      (@comm_ring_matrix_comp_left_identity_path R
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)));

symbol comm_ring_freyd_cokernel_projection_raw
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f))
≔ @comm_ring_presentation_morphism_intro R Q
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R Q))
    (@comm_ring_matrix_inl R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@comm_ring_freyd_cokernel_projection_law R P Q f);

symbol comm_ring_freyd_cokernel_projection
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f))
≔ @comm_ring_freyd_hom_class R Q
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_freyd_cokernel_projection_raw R P Q f);

symbol comm_ring_freyd_cokernel_annihilation_map
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R Q))
    (@comm_ring_presentation_morphism_map R P Q f);

symbol comm_ring_freyd_cokernel_annihilation_zero
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_zero R
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P);

symbol comm_ring_freyd_cokernel_annihilation_agreement
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphismAgreement R P
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_freyd_cokernel_annihilation_map R P Q f)
      (@comm_ring_freyd_cokernel_annihilation_zero R P Q f))
≔ @comm_ring_presentation_morphism_agreement_intro R P
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_freyd_cokernel_annihilation_map R P Q f)
    (@comm_ring_freyd_cokernel_annihilation_zero R P Q f)
    (@comm_ring_matrix_inr R
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P))
    (@eq_trans _ _
      (@comm_ring_presentation_morphism_map R P Q f)
      _
      (@comm_ring_freyd_cokernel_inr_path R P Q f)
      (@eq_trans _
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_freyd_cokernel_annihilation_map R P Q f)
        _
        (@eq_sym _ _ _
          (@comm_ring_matrix_comp_left_identity_path R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_morphism_map R P Q f)))
        (@eq_sym _ _ _
          (@comm_ring_freyd_cokernel_sub_zero_path R
            (@comm_ring_presentation_generators R
              (@comm_ring_freyd_cokernel_presentation R P Q f))
            (@comm_ring_presentation_generators R P)
            (@comm_ring_freyd_cokernel_annihilation_map R P Q f)))));

symbol comm_ring_freyd_cokernel_annihilation_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_freyd_cokernel_presentation R P Q f))
      (@comm_ring_freyd_comp R P Q
        (@comm_ring_freyd_cokernel_presentation R P Q f)
        (@comm_ring_freyd_cokernel_projection R P Q f)
        (@comm_ring_freyd_hom_class R P Q f))
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_freyd_cokernel_presentation R P Q f)))
≔ @comm_ring_freyd_agreement_path R P
    (@comm_ring_freyd_cokernel_presentation R P Q f)
    (@comm_ring_presentation_morphism_comp R P Q
      (@comm_ring_freyd_cokernel_presentation R P Q f)
      (@comm_ring_freyd_cokernel_projection_raw R P Q f) f)
    (@comm_ring_presentation_morphism_zero R P
      (@comm_ring_freyd_cokernel_presentation R P Q f))
    (@comm_ring_freyd_cokernel_annihilation_agreement R P Q f);

// Raw colift witness [W_h,H_zero] on the enlarged relation module.
symbol comm_ring_freyd_cokernel_colift_witness
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R T)
      (@nat_add
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)))
≔ @comm_ring_matrix_horizontal R
    (@comm_ring_presentation_relations R T)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_morphism_witness R Q T h)
    (@comm_ring_presentation_agreement_witness R P T
      (@comm_ring_presentation_morphism_map R P T
        (@comm_ring_presentation_morphism_comp R P Q T h f))
      (@comm_ring_presentation_morphism_map R P T
        (@comm_ring_presentation_morphism_zero R P T))
      a);

symbol comm_ring_freyd_cokernel_colift_law
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R T)
      (@nat_add
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_freyd_cokernel_colift_witness R P Q T f h a))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R Q)
        (@nat_add
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_morphism_map R Q T h)
        (@comm_ring_presentation_matrix R
          (@comm_ring_freyd_cokernel_presentation R P Q f))))
≔ @eq_trans _ _
    (@comm_ring_matrix_horizontal R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_presentation_morphism_witness R Q T h))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R T)
        (@comm_ring_presentation_agreement_witness R P T
          (@comm_ring_presentation_morphism_map R P T
            (@comm_ring_presentation_morphism_comp R P Q T h f))
          (@comm_ring_presentation_morphism_map R P T
            (@comm_ring_presentation_morphism_zero R P T))
          a)))
    _
    (@comm_ring_matrix_comp_horizontal_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_relations R T)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R T)
      (@comm_ring_presentation_morphism_witness R Q T h)
      (@comm_ring_presentation_agreement_witness R P T
        (@comm_ring_presentation_morphism_map R P T
          (@comm_ring_presentation_morphism_comp R P Q T h f))
        (@comm_ring_presentation_morphism_map R P T
          (@comm_ring_presentation_morphism_zero R P T))
        a))
    (@eq_trans _ _
      (@comm_ring_matrix_horizontal R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R Q T h)
          (@comm_ring_presentation_matrix R Q))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R Q T h)
          (@comm_ring_presentation_morphism_map R P Q f)))
      _
      (@comm_ring_matrix_horizontal_congr_path R
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R P)
        _ _ _ _
        (@comm_ring_presentation_morphism_law R Q T h)
        (@eq_trans _ _ _ _
          (@comm_ring_presentation_agreement_law R P T
            (@comm_ring_presentation_morphism_map R P T
              (@comm_ring_presentation_morphism_comp R P Q T h f))
            (@comm_ring_presentation_morphism_map R P T
              (@comm_ring_presentation_morphism_zero R P T))
            a)
          (@comm_ring_freyd_cokernel_sub_zero_path R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_morphism_map R P T
              (@comm_ring_presentation_morphism_comp R P Q T h f)))))
      (@eq_sym _ _ _
        (@comm_ring_matrix_comp_horizontal_path R
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_morphism_map R Q T h)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_presentation_morphism_map R P Q f))));

symbol comm_ring_freyd_cokernel_colift_raw
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T)
≔ @comm_ring_presentation_morphism_intro R
    (@comm_ring_freyd_cokernel_presentation R P Q f) T
    (@comm_ring_presentation_morphism_map R Q T h)
    (@comm_ring_freyd_cokernel_colift_witness R P Q T f h a)
    (@comm_ring_freyd_cokernel_colift_law R P Q T f h a);

symbol comm_ring_freyd_cokernel_colift
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T)
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_cokernel_presentation R P Q f) T
    (@comm_ring_freyd_cokernel_colift_raw R P Q T f h a);

symbol comm_ring_freyd_cokernel_reconstruction_agreement
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  : τ (@CommRingPresentationMorphismAgreement R Q T
      (@comm_ring_presentation_morphism_map R Q T
        (@comm_ring_presentation_morphism_comp R Q
          (@comm_ring_freyd_cokernel_presentation R P Q f) T
          (@comm_ring_freyd_cokernel_colift_raw R P Q T f h a)
          (@comm_ring_freyd_cokernel_projection_raw R P Q f)))
      (@comm_ring_presentation_morphism_map R Q T h))
≔ @comm_ring_presentation_agreement_of_map_path R Q T _ _
    (@comm_ring_matrix_comp_right_identity_path R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_morphism_map R Q T h));

symbol comm_ring_freyd_cokernel_reconstruction_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (h : τ (@CommRingPresentationMorphism R Q T))
  (a : τ (@CommRingPresentationMorphismAgreement R P T
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_comp R P Q T h f))
    (@comm_ring_presentation_morphism_map R P T
      (@comm_ring_presentation_morphism_zero R P T))))
  : τ (@= (@CommRingFreydHomSet R Q T)
      (@comm_ring_freyd_comp R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f) T
        (@comm_ring_freyd_cokernel_colift R P Q T f h a)
        (@comm_ring_freyd_cokernel_projection R P Q f))
      (@comm_ring_freyd_hom_class R Q T h))
≔ @comm_ring_freyd_agreement_path R Q T
    (@comm_ring_presentation_morphism_comp R Q
      (@comm_ring_freyd_cokernel_presentation R P Q f) T
      (@comm_ring_freyd_cokernel_colift_raw R P Q T f h a)
      (@comm_ring_freyd_cokernel_projection_raw R P Q f))
    h
    (@comm_ring_freyd_cokernel_reconstruction_agreement R P Q T f h a);

// A competing raw colift reconstructing h is agreement-equal to the selected one.
symbol comm_ring_freyd_cokernel_uniqueness_agreement
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_cokernel_presentation R P Q f) T k)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_cokernel_presentation R P Q f) T
        (@comm_ring_freyd_cokernel_colift_raw R P Q T f h a)))
≔ @comm_ring_presentation_agreement_trans R
    (@comm_ring_freyd_cokernel_presentation R P Q f) T
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T k)
    (@comm_ring_presentation_morphism_map R Q T
      (@comm_ring_presentation_morphism_comp R Q
        (@comm_ring_freyd_cokernel_presentation R P Q f) T
        k (@comm_ring_freyd_cokernel_projection_raw R P Q f)))
    (@comm_ring_presentation_morphism_map R Q T h)
    (@comm_ring_presentation_agreement_of_map_path R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T _ _
      (@eq_sym _ _ _
        (@comm_ring_matrix_comp_right_identity_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R
            (@comm_ring_freyd_cokernel_presentation R P Q f) T k))))
    reconstructs;

symbol comm_ring_freyd_cokernel_uniqueness_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
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
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_cokernel_presentation R P Q f) T)
      (@comm_ring_freyd_hom_class R
        (@comm_ring_freyd_cokernel_presentation R P Q f) T k)
      (@comm_ring_freyd_cokernel_colift R P Q T f h a))
≔ @comm_ring_freyd_agreement_path R
    (@comm_ring_freyd_cokernel_presentation R P Q f) T
    k
    (@comm_ring_freyd_cokernel_colift_raw R P Q T f h a)
    (@comm_ring_freyd_cokernel_uniqueness_agreement
      R P Q T f h a k reconstructs);
