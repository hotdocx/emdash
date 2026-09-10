/* Model-owned records at the EXACT existing concrete-consumer H points.
   Thin specialization of the whole K/Q/H record, not a new homology. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_models;
require open emdash.emdash3_2_chain_pair_homology_records;

symbol freyd_homology_model_record [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@HomologyRecord (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain))
≔ @chain_pair_homology_record (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
  (@freyd_homology_model_initial R M) (@freyd_homology_model_kernels R M) (@freyd_homology_model_cokernels R M)
  (@freyd_homology_model_kernel_presentation R M) (@freyd_homology_model_cokernel_presentation R M) A B D
  (@freyd_raw_chain_pair_generic R A B D e d chain);
