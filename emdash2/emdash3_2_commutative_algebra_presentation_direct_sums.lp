/*
  Zero and binary direct sums of finite presentations.

  Presentation sums use block-diagonal relation matrices. Raw direct sums,
  projections, and pairing retain both generator and relation matrices. Every
  stored relation square is constructed from the flattened block laws and the
  input squares; no manual commuting-square field is accepted.
*/

require open emdash.emdash3_2_commutative_algebra_finite_free_direct_sums;
require open emdash.emdash3_2_commutative_algebra_presentation_operations;

// The zero presentation `[0 : R^0 -> R^0]`.
symbol comm_ring_zero_presentation
  (R : τ CommRing)
  : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R zero zero
    (@comm_ring_matrix_zero R zero zero);

// Binary direct sum of presentations by a block-diagonal relation matrix.
symbol comm_ring_presentation_direct_sum
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R
    (@nat_add
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q))
    (@nat_add
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q))
    (@comm_ring_matrix_block_diag R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_presentation_matrix R Q));

// Generator matrix of a raw direct-sum morphism.
symbol comm_ring_presentation_morphism_direct_sum_map
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P0 Q0))
  (g : τ (@CommRingPresentationMorphism R P1 Q1))
  : τ (@CommRingMatrix R
      (@nat_add
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1))
      (@nat_add
        (@comm_ring_presentation_generators R P0)
        (@comm_ring_presentation_generators R P1)))
≔ @comm_ring_matrix_block_diag R
    (@comm_ring_presentation_generators R Q0)
    (@comm_ring_presentation_generators R Q1)
    (@comm_ring_presentation_generators R P0)
    (@comm_ring_presentation_generators R P1)
    (@comm_ring_presentation_morphism_map R P0 Q0 f)
    (@comm_ring_presentation_morphism_map R P1 Q1 g);

// Relation-witness matrix of a raw direct-sum morphism.
symbol comm_ring_presentation_morphism_direct_sum_witness
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P0 Q0))
  (g : τ (@CommRingPresentationMorphism R P1 Q1))
  : τ (@CommRingMatrix R
      (@nat_add
        (@comm_ring_presentation_relations R Q0)
        (@comm_ring_presentation_relations R Q1))
      (@nat_add
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_relations R P1)))
≔ @comm_ring_matrix_block_diag R
    (@comm_ring_presentation_relations R Q0)
    (@comm_ring_presentation_relations R Q1)
    (@comm_ring_presentation_relations R P0)
    (@comm_ring_presentation_relations R P1)
    (@comm_ring_presentation_morphism_witness R P0 Q0 f)
    (@comm_ring_presentation_morphism_witness R P1 Q1 g);

// The direct-sum square is blockwise composition plus the two input squares.
symbol comm_ring_presentation_morphism_direct_sum_law
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P0 Q0))
  (g : τ (@CommRingPresentationMorphism R P1 Q1))
  : τ (@= (@CommRingMatrix R
      (@nat_add
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1))
      (@nat_add
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_relations R P1)))
    (@comm_ring_matrix_comp R
      (@nat_add
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1))
      (@nat_add
        (@comm_ring_presentation_relations R Q0)
        (@comm_ring_presentation_relations R Q1))
      (@nat_add
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_relations R P1))
      (@comm_ring_presentation_matrix R
        (@comm_ring_presentation_direct_sum R Q0 Q1))
      (@comm_ring_presentation_morphism_direct_sum_witness
        R P0 P1 Q0 Q1 f g))
    (@comm_ring_matrix_comp R
      (@nat_add
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1))
      (@nat_add
        (@comm_ring_presentation_generators R P0)
        (@comm_ring_presentation_generators R P1))
      (@nat_add
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_relations R P1))
      (@comm_ring_presentation_morphism_direct_sum_map
        R P0 P1 Q0 Q1 f g)
      (@comm_ring_presentation_matrix R
        (@comm_ring_presentation_direct_sum R P0 P1))))
≔ @eq_trans
    _
    _
    (@comm_ring_matrix_block_diag R
      (@comm_ring_presentation_generators R Q0)
      (@comm_ring_presentation_generators R Q1)
      (@comm_ring_presentation_relations R P0)
      (@comm_ring_presentation_relations R P1)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_relations R Q0)
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_matrix R Q0)
        (@comm_ring_presentation_morphism_witness R P0 Q0 f))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q1)
        (@comm_ring_presentation_relations R Q1)
        (@comm_ring_presentation_relations R P1)
        (@comm_ring_presentation_matrix R Q1)
        (@comm_ring_presentation_morphism_witness R P1 Q1 g)))
    _
    (@comm_ring_matrix_block_diag_comp_path R
      (@comm_ring_presentation_generators R Q0)
      (@comm_ring_presentation_generators R Q1)
      (@comm_ring_presentation_relations R Q0)
      (@comm_ring_presentation_relations R Q1)
      (@comm_ring_presentation_relations R P0)
      (@comm_ring_presentation_relations R P1)
      (@comm_ring_presentation_matrix R Q0)
      (@comm_ring_presentation_matrix R Q1)
      (@comm_ring_presentation_morphism_witness R P0 Q0 f)
      (@comm_ring_presentation_morphism_witness R P1 Q1 g))
    (@eq_trans
      _
      _
      (@comm_ring_matrix_block_diag R
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1)
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_relations R P1)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q0)
          (@comm_ring_presentation_generators R P0)
          (@comm_ring_presentation_relations R P0)
          (@comm_ring_presentation_morphism_map R P0 Q0 f)
          (@comm_ring_presentation_matrix R P0))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q1)
          (@comm_ring_presentation_generators R P1)
          (@comm_ring_presentation_relations R P1)
          (@comm_ring_presentation_morphism_map R P1 Q1 g)
          (@comm_ring_presentation_matrix R P1)))
      _
      (@comm_ring_matrix_block_diag_congr_path R
        (@comm_ring_presentation_generators R Q0)
        (@comm_ring_presentation_generators R Q1)
        (@comm_ring_presentation_relations R P0)
        (@comm_ring_presentation_relations R P1)
        _ _ _ _
        (@comm_ring_presentation_morphism_law R P0 Q0 f)
        (@comm_ring_presentation_morphism_law R P1 Q1 g))
      (@eq_sym _ _ _
        (@comm_ring_matrix_block_diag_comp_path R
          (@comm_ring_presentation_generators R Q0)
          (@comm_ring_presentation_generators R Q1)
          (@comm_ring_presentation_generators R P0)
          (@comm_ring_presentation_generators R P1)
          (@comm_ring_presentation_relations R P0)
          (@comm_ring_presentation_relations R P1)
          (@comm_ring_presentation_morphism_map R P0 Q0 f)
          (@comm_ring_presentation_morphism_map R P1 Q1 g)
          (@comm_ring_presentation_matrix R P0)
          (@comm_ring_presentation_matrix R P1))));

// Whole raw direct-sum morphism retaining both matrices and the derived square.
symbol comm_ring_presentation_morphism_direct_sum
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P0 Q0))
  (g : τ (@CommRingPresentationMorphism R P1 Q1))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_presentation_direct_sum R P0 P1)
      (@comm_ring_presentation_direct_sum R Q0 Q1))
≔ @comm_ring_presentation_morphism_intro R
    (@comm_ring_presentation_direct_sum R P0 P1)
    (@comm_ring_presentation_direct_sum R Q0 Q1)
    (@comm_ring_presentation_morphism_direct_sum_map
      R P0 P1 Q0 Q1 f g)
    (@comm_ring_presentation_morphism_direct_sum_witness
      R P0 P1 Q0 Q1 f g)
    (@comm_ring_presentation_morphism_direct_sum_law
      R P0 P1 Q0 Q1 f g);

// First raw projection relation square.
symbol comm_ring_presentation_proj1_law
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_matrix_proj1 R
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@nat_add
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_proj1 R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_presentation_matrix R
        (@comm_ring_presentation_direct_sum R P Q))))
≔ @comm_ring_matrix_block_diag_proj1_path R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_presentation_matrix R Q);

// First raw projection `P⊕Q -> P`.
symbol comm_ring_presentation_proj1
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_presentation_direct_sum R P Q) P)
≔ @comm_ring_presentation_morphism_intro R
    (@comm_ring_presentation_direct_sum R P Q) P
    (@comm_ring_matrix_proj1 R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q))
    (@comm_ring_matrix_proj1 R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q))
    (@comm_ring_presentation_proj1_law R P Q);

// Second raw projection relation square.
symbol comm_ring_presentation_proj2_law
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_matrix_proj2 R
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@nat_add
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_matrix_proj2 R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_presentation_matrix R
        (@comm_ring_presentation_direct_sum R P Q))))
≔ @comm_ring_matrix_block_diag_proj2_path R
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_presentation_matrix R Q);

// Second raw projection `P⊕Q -> Q`.
symbol comm_ring_presentation_proj2
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_presentation_direct_sum R P Q) Q)
≔ @comm_ring_presentation_morphism_intro R
    (@comm_ring_presentation_direct_sum R P Q) Q
    (@comm_ring_matrix_proj2 R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q))
    (@comm_ring_matrix_proj2 R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q))
    (@comm_ring_presentation_proj2_law R P Q);

// Pairing relation square is the vertical combination of the two input squares.
symbol comm_ring_presentation_pair_law
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R X P))
  (g : τ (@CommRingPresentationMorphism R X Q))
  : τ (@= (@CommRingMatrix R
      (@nat_add
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_presentation_relations R X))
    (@comm_ring_matrix_comp R
      (@nat_add
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@nat_add
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q))
      (@comm_ring_presentation_relations R X)
      (@comm_ring_presentation_matrix R
        (@comm_ring_presentation_direct_sum R P Q))
      (@comm_ring_matrix_vertical R
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R X)
        (@comm_ring_presentation_morphism_witness R X P f)
        (@comm_ring_presentation_morphism_witness R X Q g)))
    (@comm_ring_matrix_comp R
      (@nat_add
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q))
      (@comm_ring_presentation_generators R X)
      (@comm_ring_presentation_relations R X)
      (@comm_ring_matrix_vertical R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R X)
        (@comm_ring_presentation_morphism_map R X P f)
        (@comm_ring_presentation_morphism_map R X Q g))
      (@comm_ring_presentation_matrix R X)))
≔ @eq_trans
    _ _
    (@comm_ring_matrix_vertical R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R X)
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R X)
        (@comm_ring_presentation_matrix R P)
        (@comm_ring_presentation_morphism_witness R X P f))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_relations R X)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R X Q g)))
    _
    (@comm_ring_matrix_block_diag_vertical_path R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R X)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_witness R X P f)
      (@comm_ring_presentation_morphism_witness R X Q g))
    (@eq_trans
      _ _
      (@comm_ring_matrix_vertical R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R X)
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_presentation_relations R X)
          (@comm_ring_presentation_morphism_map R X P f)
          (@comm_ring_presentation_matrix R X))
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_presentation_relations R X)
          (@comm_ring_presentation_morphism_map R X Q g)
          (@comm_ring_presentation_matrix R X)))
      _
      (@comm_ring_matrix_vertical_congr_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R X)
        _ _ _ _
        (@comm_ring_presentation_morphism_law R X P f)
        (@comm_ring_presentation_morphism_law R X Q g))
      (@eq_sym _ _ _
        (@comm_ring_matrix_vertical_comp_path R
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R X)
          (@comm_ring_presentation_relations R X)
          (@comm_ring_presentation_morphism_map R X P f)
          (@comm_ring_presentation_morphism_map R X Q g)
          (@comm_ring_presentation_matrix R X))));

// Whole raw pairing `<f,g> : X -> P⊕Q`.
symbol comm_ring_presentation_pair
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R X P))
  (g : τ (@CommRingPresentationMorphism R X Q))
  : τ (@CommRingPresentationMorphism R X
      (@comm_ring_presentation_direct_sum R P Q))
≔ @comm_ring_presentation_morphism_intro R X
    (@comm_ring_presentation_direct_sum R P Q)
    (@comm_ring_matrix_vertical R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R X)
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X Q g))
    (@comm_ring_matrix_vertical R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R X)
      (@comm_ring_presentation_morphism_witness R X P f)
      (@comm_ring_presentation_morphism_witness R X Q g))
    (@comm_ring_presentation_pair_law R X P Q f g);
