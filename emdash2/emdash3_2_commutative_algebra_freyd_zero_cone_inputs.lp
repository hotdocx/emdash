require open emdash.emdash3_2_chain_pair_zero_cones;
require open emdash.emdash3_2_commutative_algebra_freyd_homology;
require open emdash.emdash3_2_commutative_algebra_freyd_preadditive;
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cones;
require open emdash.emdash3_2_zero_arrow_cone_homology;

/* The existing raw chain agreement supplies the generic chain-pair input. */

symbol freyd_raw_chain_zero_path [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@= (@CommRingFreydHomSet R A D)
      (@comp_fapp0 (@CommRingFreydPresentation_cat R) A B D
        (@comm_ring_freyd_hom_class R B D d) (@comm_ring_freyd_hom_class R A B e))
      (@comm_ring_freyd_zero_class R A D))
≔ @eq_trans (@CommRingFreydHomSet R A D) _ _ _
    (@comm_ring_freyd_comp_usability_path R A B D
      (@comm_ring_freyd_hom_class R B D d) (@comm_ring_freyd_hom_class R A B e))
    (@comm_ring_freyd_agreement_path R A D
      (@comm_ring_presentation_morphism_comp R A B D d e)
      (@comm_ring_presentation_morphism_zero R A D) chain);

symbol freyd_raw_chain_pair_generic [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@ComputationalChainPair (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive R) A B D)
≔ @computational_chain_pair_intro (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) A B D
    (@comm_ring_freyd_hom_class R A B e) (@comm_ring_freyd_hom_class R B D d)
    (@freyd_raw_chain_zero_path R A B D e d chain);

/* Existing raw Freyd inputs enter the whole native interface.
   W/P remain explicit model capabilities; no closed provider is inferred. */

symbol freyd_raw_chain_zero_cone [R : τ CommRing]
  [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
≔ @chain_pair_zero_cone (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W P A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain);

/* Whole model-facing H. The existing ordinary profile and canonical
   preadditive/terminal data are filled here; coherent P/Q stay explicit. */
symbol freyd_zero_cone_homology_func [R : τ CommRing]
  [T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R))
    (@comm_ring_zero_presentation R))]
  [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R))]
  [V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R) W))
  (Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) T0 V))
  : τ (Functor
      (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@CommRingFreydPresentation_cat R))
≔ @zero_arrow_cone_homology_func (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
    T0 W V P Q;
