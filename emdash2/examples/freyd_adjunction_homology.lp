/* Whole structures remain explicit; the original raw input is retained. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_homology;

// The record observes the actual whole H at the direct native input.
assert [R : τ CommRing]
  [T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))]
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) T0))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_raw_chain_adjunction_homology_record R T0 P Q A B D e d chain)
  ≡ @fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_zero_cone_adjunction_homology_func R T0 P Q) (@freyd_raw_chain_native_cone R A B D e d chain);

// Its actual boundary reconstructs the original raw incoming class.
assert [R : τ CommRing]
  [T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))]
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) T0))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @homology_record_boundary_path (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_raw_chain_adjunction_homology_record R T0 P Q A B D e d chain)
  : τ (@= (@CommRingFreydHomSet R A B)
    (@comp_fapp0 (@CommRingFreydPresentation_cat R) A (@homology_record_cycle_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_raw_chain_adjunction_homology_record R T0 P Q A B D e d chain)) B (@homology_record_cycle_embedding (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_raw_chain_adjunction_homology_record R T0 P Q A B D e d chain)) (@homology_record_boundary (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain) (@freyd_raw_chain_adjunction_homology_record R T0 P Q A B D e d chain)))
    (@comm_ring_freyd_hom_class R A B e));
