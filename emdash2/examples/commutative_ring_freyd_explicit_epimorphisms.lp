/* Existing witness, retained coefficient blocks, and law/endpoints negatives. */

require open emdash.emdash3_2_commutative_algebra_freyd_explicit_epimorphisms;

symbol R : τ CommRing;
symbol p : τ Nat_grpd;
symbol pr : τ Nat_grpd;
symbol q : τ Nat_grpd;
symbol qr : τ Nat_grpd;
symbol P : τ (@CommRingMatrix R p pr);
symbol Q : τ (@CommRingMatrix R q qr);
symbol F : τ (@CommRingMatrix R q p);
symbol W : τ (@CommRingMatrix R qr pr);
symbol lawF : τ (@= (@CommRingMatrix R q pr)
  (@comm_ring_matrix_comp R q qr pr Q W)
  (@comm_ring_matrix_comp R q p pr F P));
symbol U : τ (@CommRingMatrix R qr q);
symbol V : τ (@CommRingMatrix R p q);
symbol lawE : τ (@= (@CommRingMatrix R q q)
  (@comm_ring_matrix_add R q q
    (@comm_ring_matrix_comp R q qr q Q U)
    (@comm_ring_matrix_comp R q p q F V))
  (@comm_ring_finite_free_id_matrix R q));

symbol SP : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R p pr P;
symbol SQ : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R q qr Q;
symbol f : τ (@CommRingPresentationMorphism R SP SQ)
≔ @comm_ring_presentation_morphism_from_matrices R
  p pr q qr P Q F W lawF;
symbol e : τ (@CommRingFreydEpimorphismWitness R SP SQ f)
≔ @comm_ring_freyd_epimorphism_from_matrices R
  p pr q qr P Q F W lawF U V lawE;

assert ⊢ e : τ (@CommRingFreydEpimorphismWitness R SP SQ f);
assert ⊢ @comm_ring_presentation_morphism_map R SP SQ f ≡ F;
assert ⊢ @comm_ring_presentation_morphism_witness R SP SQ f ≡ W;
assert ⊢ @comm_ring_presentation_morphism_law R SP SQ f ≡ lawF;
assert ⊢ @comm_ring_freyd_epimorphism_witness R SP SQ f e
  ≡ @comm_ring_matrix_vertical R qr p q U V;

// Arbitrary-rank matrix block projections compare by the existing paths.
assert ⊢ @comm_ring_matrix_proj1_vertical_path R qr p q U V
  : τ (@= (@CommRingMatrix R qr q)
      (@comm_ring_freyd_epimorphism_target_component R SP SQ f e) U);
assert ⊢ @comm_ring_matrix_proj2_vertical_path R qr p q U V
  : τ (@= (@CommRingMatrix R p q)
      (@comm_ring_freyd_epimorphism_source_component R SP SQ f e) V);
assert ⊢ @comm_ring_freyd_epimorphism_block_path R SP SQ f e
  : τ (@= (@CommRingMatrix R q q)
      (@comm_ring_matrix_add R q q
        (@comm_ring_matrix_comp R q qr q Q
          (@comm_ring_freyd_epimorphism_target_component R SP SQ f e))
        (@comm_ring_matrix_comp R q p q F
          (@comm_ring_freyd_epimorphism_source_component R SP SQ f e)))
      (@comm_ring_finite_free_id_matrix R q));

// The right matrix dimension alone does not make an unrelated law valid.
assertnot ⊢ @comm_ring_freyd_epimorphism_from_matrices R
  p pr q qr P Q F W lawF U V
  (@eq_refl (@CommRingMatrix R q q) (@comm_ring_finite_free_id_matrix R q))
  : τ (@CommRingFreydEpimorphismWitness R SP SQ f);
assertnot ⊢ @comm_ring_freyd_epimorphism_from_matrices R
  p pr q qr P Q F W lawF U V lawF
  : τ (@CommRingFreydEpimorphismWitness R SP SQ f);
assertnot ⊢ e : τ (@CommRingFreydEpimorphismWitness R SP SP
  (@comm_ring_presentation_morphism_zero R SP SP));
