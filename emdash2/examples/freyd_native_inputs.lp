/* Raw Freyd data forms native input with no W/P/Q parameters. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_inputs;
require open emdash.emdash3_2_zero_arrow_diagram_observations;

// The first native vertex is the original presentation.
assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R A B D e d chain)
  ≡ A;

// The incoming arrow is the class of the original raw morphism.
assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @terminal_arrow_test_incoming (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) A (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R A B D e d chain)) (@tapp0_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) _ _ (@freyd_raw_chain_native_cone R A B D e d chain) (@freyd_zero_cone_universal_transf R))
  ≡ @comm_ring_freyd_hom_class R A B e;

// The outgoing arrow is the class of the original raw morphism.
assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @fapp1_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R A B D e d chain)) walking_arrow_src walking_arrow_tgt walking_arrow_generator
  ≡ @comm_ring_freyd_hom_class R B D d;

// The generic pair retains the existing raw-agreement observation.
assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @computational_chain_pair_path (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) A B D (@freyd_raw_chain_pair_generic R A B D e d chain)
  ≡ @freyd_raw_chain_zero_path R A B D e d chain;
