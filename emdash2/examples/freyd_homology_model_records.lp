/* The connecting consumer reuses exactly its original supplied-model H. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_records;

assert [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢ (@freyd_homology_model_record R M A B D e d chain)
  : τ (@HomologyRecord (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain));


assert [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_homology_model_record R M A B D e d chain)
  ≡ @freyd_homology_model_object R M A B D e d chain;

// Distinct model selections are not collapsed by the record adapter.
assertnot [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) (N : τ (FreydHomologyModel R)) ⊢
  @homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_homology_model_record R M A B D e d chain)
  ≡ @freyd_homology_model_object R N A B D e d chain;
