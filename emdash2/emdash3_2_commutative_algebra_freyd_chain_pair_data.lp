/* Raw agreement observations shared by both input presentations.
   This module uses record vocabulary but performs no universal selection. */
require open emdash.emdash3_2_computational_homology;
require open emdash.emdash3_2_commutative_algebra_presentation_chain_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_preadditive;

// The original raw agreement, viewed as the generic chain-zero path.
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

// Retain the original two quotient classes and chain-zero observation.
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
