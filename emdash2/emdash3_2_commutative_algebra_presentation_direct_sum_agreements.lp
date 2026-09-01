/*
  Agreement compatibility for presentation direct sums and pairing.

  Target-factorization witnesses combine by flattened block diagonal for
  direct-sum maps and by vertical pairing for maps into a presentation sum.
  Their laws are constructed from block composition/subtraction and the input
  agreement laws. No quotient operation or runtime rule is introduced here.
*/

require open emdash.emdash3_2_commutative_algebra_presentation_direct_sums;
require open emdash.emdash3_2_commutative_algebra_presentation_agreement_operations;

// Agreement between two block-diagonal raw direct-sum maps.
symbol comm_ring_presentation_direct_sum_agreement
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R P0 Q0)]
  [g g' : τ (@CommRingPresentationMorphism R P1 Q1)]
  (a : τ (@CommRingPresentationMorphismAgreement R P0 Q0
      (@comm_ring_presentation_morphism_map R P0 Q0 f)
      (@comm_ring_presentation_morphism_map R P0 Q0 f')))
  (b : τ (@CommRingPresentationMorphismAgreement R P1 Q1
      (@comm_ring_presentation_morphism_map R P1 Q1 g)
      (@comm_ring_presentation_morphism_map R P1 Q1 g')))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_presentation_direct_sum R P0 P1)
      (@comm_ring_presentation_direct_sum R Q0 Q1)
      (@comm_ring_presentation_morphism_direct_sum_map
        R P0 P1 Q0 Q1 f g)
      (@comm_ring_presentation_morphism_direct_sum_map
        R P0 P1 Q0 Q1 f' g'))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_presentation_direct_sum R P0 P1)
    (@comm_ring_presentation_direct_sum R Q0 Q1)
    (@comm_ring_presentation_morphism_direct_sum_map
      R P0 P1 Q0 Q1 f g)
    (@comm_ring_presentation_morphism_direct_sum_map
      R P0 P1 Q0 Q1 f' g')
    (@comm_ring_matrix_block_diag R
      (@comm_ring_presentation_relations R Q0)
      (@comm_ring_presentation_relations R Q1)
      (@comm_ring_presentation_generators R P0)
      (@comm_ring_presentation_generators R P1)
      (@comm_ring_presentation_agreement_witness R P0 Q0
        (@comm_ring_presentation_morphism_map R P0 Q0 f)
        (@comm_ring_presentation_morphism_map R P0 Q0 f') a)
      (@comm_ring_presentation_agreement_witness R P1 Q1
        (@comm_ring_presentation_morphism_map R P1 Q1 g)
        (@comm_ring_presentation_morphism_map R P1 Q1 g') b))
    (@eq_trans
      _ _
      (@comm_ring_matrix_block_diag R
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1)
        (@comm_ring_presentation_generators R P0)
        (@comm_ring_presentation_generators R P1)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q0)
          (@comm_ring_presentation_relations R Q0)
          (@comm_ring_presentation_generators R P0)
          (@comm_ring_presentation_matrix R Q0)
          (@comm_ring_presentation_agreement_witness R P0 Q0
            (@comm_ring_presentation_morphism_map R P0 Q0 f)
            (@comm_ring_presentation_morphism_map R P0 Q0 f') a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q1)
          (@comm_ring_presentation_relations R Q1)
          (@comm_ring_presentation_generators R P1)
          (@comm_ring_presentation_matrix R Q1)
          (@comm_ring_presentation_agreement_witness R P1 Q1
            (@comm_ring_presentation_morphism_map R P1 Q1 g)
            (@comm_ring_presentation_morphism_map R P1 Q1 g') b)))
      _
      (@comm_ring_matrix_block_diag_comp_path R
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1)
        (@comm_ring_presentation_relations R Q0)
        (@comm_ring_presentation_relations R Q1)
        (@comm_ring_presentation_generators R P0)
        (@comm_ring_presentation_generators R P1)
        (@comm_ring_presentation_matrix R Q0)
        (@comm_ring_presentation_matrix R Q1)
        (@comm_ring_presentation_agreement_witness R P0 Q0
          (@comm_ring_presentation_morphism_map R P0 Q0 f)
          (@comm_ring_presentation_morphism_map R P0 Q0 f') a)
        (@comm_ring_presentation_agreement_witness R P1 Q1
          (@comm_ring_presentation_morphism_map R P1 Q1 g)
          (@comm_ring_presentation_morphism_map R P1 Q1 g') b))
      (@eq_trans
        _ _
        (@comm_ring_matrix_block_diag R
          (@comm_ring_presentation_generators R Q0)
          (@comm_ring_presentation_generators R Q1)
          (@comm_ring_presentation_generators R P0)
          (@comm_ring_presentation_generators R P1)
          (@comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R Q0)
            (@comm_ring_presentation_generators R P0)
            (@comm_ring_presentation_morphism_map R P0 Q0 f)
            (@comm_ring_presentation_morphism_map R P0 Q0 f'))
          (@comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R Q1)
            (@comm_ring_presentation_generators R P1)
            (@comm_ring_presentation_morphism_map R P1 Q1 g)
            (@comm_ring_presentation_morphism_map R P1 Q1 g')))
        _
        (@comm_ring_matrix_block_diag_congr_path R
          (@comm_ring_presentation_generators R Q0)
          (@comm_ring_presentation_generators R Q1)
          (@comm_ring_presentation_generators R P0)
          (@comm_ring_presentation_generators R P1)
          _ _ _ _
          (@comm_ring_presentation_agreement_law R P0 Q0
            (@comm_ring_presentation_morphism_map R P0 Q0 f)
            (@comm_ring_presentation_morphism_map R P0 Q0 f') a)
          (@comm_ring_presentation_agreement_law R P1 Q1
            (@comm_ring_presentation_morphism_map R P1 Q1 g)
            (@comm_ring_presentation_morphism_map R P1 Q1 g') b))
        (@comm_ring_matrix_block_diag_sub_path R
          (@comm_ring_presentation_generators R Q0)
          (@comm_ring_presentation_generators R Q1)
          (@comm_ring_presentation_generators R P0)
          (@comm_ring_presentation_generators R P1)
          (@comm_ring_presentation_morphism_map R P0 Q0 f)
          (@comm_ring_presentation_morphism_map R P0 Q0 f')
          (@comm_ring_presentation_morphism_map R P1 Q1 g)
          (@comm_ring_presentation_morphism_map R P1 Q1 g'))));

// Agreement between two vertically paired raw maps.
symbol comm_ring_presentation_pair_agreement
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R X P)]
  [g g' : τ (@CommRingPresentationMorphism R X Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  (b : τ (@CommRingPresentationMorphismAgreement R X Q
      (@comm_ring_presentation_morphism_map R X Q g)
      (@comm_ring_presentation_morphism_map R X Q g')))
  : τ (@CommRingPresentationMorphismAgreement R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f g))
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f' g')))
≔ @comm_ring_presentation_morphism_agreement_intro R X
    (@comm_ring_presentation_direct_sum R P Q)
    (@comm_ring_presentation_morphism_map R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_pair R X P Q f g))
    (@comm_ring_presentation_morphism_map R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_pair R X P Q f' g'))
    (@comm_ring_matrix_vertical R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R X)
      (@comm_ring_presentation_agreement_witness R X P
        (@comm_ring_presentation_morphism_map R X P f)
        (@comm_ring_presentation_morphism_map R X P f') a)
      (@comm_ring_presentation_agreement_witness R X Q
        (@comm_ring_presentation_morphism_map R X Q g)
        (@comm_ring_presentation_morphism_map R X Q g') b))
    (@eq_trans
      _ _
      (@comm_ring_matrix_vertical R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R X)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_presentation_matrix R P)
          (@comm_ring_presentation_agreement_witness R X P
            (@comm_ring_presentation_morphism_map R X P f)
            (@comm_ring_presentation_morphism_map R X P f') a))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_presentation_agreement_witness R X Q
            (@comm_ring_presentation_morphism_map R X Q g)
            (@comm_ring_presentation_morphism_map R X Q g') b)))
      _
      (@comm_ring_matrix_block_diag_vertical_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R X)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R X P
          (@comm_ring_presentation_morphism_map R X P f)
          (@comm_ring_presentation_morphism_map R X P f') a)
        (@comm_ring_presentation_agreement_witness R X Q
          (@comm_ring_presentation_morphism_map R X Q g)
          (@comm_ring_presentation_morphism_map R X Q g') b))
      (@eq_trans
        _ _
        (@comm_ring_matrix_vertical R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R P)
            (@comm_ring_presentation_generators R X)
            (@comm_ring_presentation_morphism_map R X P f)
            (@comm_ring_presentation_morphism_map R X P f'))
          (@comm_ring_matrix_sub R
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_generators R X)
            (@comm_ring_presentation_morphism_map R X Q g)
            (@comm_ring_presentation_morphism_map R X Q g')))
        _
        (@comm_ring_matrix_vertical_congr_path R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R X)
          _ _ _ _
          (@comm_ring_presentation_agreement_law R X P
            (@comm_ring_presentation_morphism_map R X P f)
            (@comm_ring_presentation_morphism_map R X P f') a)
          (@comm_ring_presentation_agreement_law R X Q
            (@comm_ring_presentation_morphism_map R X Q g)
            (@comm_ring_presentation_morphism_map R X Q g') b))
        (@comm_ring_matrix_vertical_sub_path R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_presentation_morphism_map R X P f)
          (@comm_ring_presentation_morphism_map R X P f')
          (@comm_ring_presentation_morphism_map R X Q g)
          (@comm_ring_presentation_morphism_map R X Q g'))));
