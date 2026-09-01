/*
  Formal identity and composition of relation-preserving presentations.

  A raw map retains generator matrix F, relation matrix W, and the internally
  derived square R_Q o W = F o R_P. Identity uses the selected finite-free
  matrix identities. Composition pastes the two stored squares through the
  checked transparent matrix associativity theorem. No runtime category rule,
  quotient equality, or opaque coherence witness is introduced here.
*/

require open emdash.emdash3_2_commutative_algebra_finite_free_category;

// The presentation matrix commutes with the two selected identity matrices.
symbol comm_ring_presentation_identity_law
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_relations R P)))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_matrix R P)))
≔ @eq_trans
    (@CommRingMatrix R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_relations R P)))
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_finite_free_id_matrix R
        (@comm_ring_presentation_generators R P))
      (@comm_ring_presentation_matrix R P))
    (@comm_ring_matrix_comp_right_identity_path R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_matrix R P))
    (@eq_sym
      (@CommRingMatrix R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P))
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_finite_free_id_matrix R
          (@comm_ring_presentation_generators R P))
        (@comm_ring_presentation_matrix R P))
      (@comm_ring_presentation_matrix R P)
      (@comm_ring_matrix_comp_left_identity_path R
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_matrix R P)));

// Raw presentation identity: the identities on generators and relations.
symbol comm_ring_presentation_morphism_identity
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@CommRingPresentationMorphism R P P)
≔ @comm_ring_presentation_morphism_intro R P P
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_generators R P))
    (@comm_ring_finite_free_id_matrix R
      (@comm_ring_presentation_relations R P))
    (@comm_ring_presentation_identity_law R P);

// Generator and relation parts of raw presentation composition.
symbol comm_ring_presentation_morphism_comp_map
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R P))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_generators R S)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_morphism_map R Q S g)
    (@comm_ring_presentation_morphism_map R P Q f);

symbol comm_ring_presentation_morphism_comp_witness
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingMatrix R
      (@comm_ring_presentation_relations R S)
      (@comm_ring_presentation_relations R P))
≔ @comm_ring_matrix_comp R
    (@comm_ring_presentation_relations R S)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_morphism_witness R Q S g)
    (@comm_ring_presentation_morphism_witness R P Q f);

// The composite square is derived by the generic matrix-square pasting path.
symbol comm_ring_presentation_morphism_comp_law
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_relations R P))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_relations R S)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R S)
      (@comm_ring_presentation_morphism_comp_witness R P Q S g f))
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R S)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_morphism_comp_map R P Q S g f)
      (@comm_ring_presentation_matrix R P)))
≔ @comm_ring_matrix_square_comp_path R
    (@comm_ring_presentation_relations R P)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R S)
    (@comm_ring_presentation_generators R S)
    (@comm_ring_presentation_matrix R P)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_presentation_matrix R S)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_morphism_witness R P Q f)
    (@comm_ring_presentation_morphism_map R Q S g)
    (@comm_ring_presentation_morphism_witness R Q S g)
    (@comm_ring_presentation_morphism_law R P Q f)
    (@comm_ring_presentation_morphism_law R Q S g);

// Whole raw composite retaining both matrices and the derived square law.
symbol comm_ring_presentation_morphism_comp
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingPresentationMorphism R P S)
≔ @comm_ring_presentation_morphism_intro R P S
    (@comm_ring_presentation_morphism_comp_map R P Q S g f)
    (@comm_ring_presentation_morphism_comp_witness R P Q S g f)
    (@comm_ring_presentation_morphism_comp_law R P Q S g f);
