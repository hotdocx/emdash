/* Quotient-class entry retains the original raw representatives/agreement. */
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cone_inputs;
require open emdash.emdash3_2_chain_pair_zero_cone_comparisons;

assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @computational_chain_pair_dnext (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain)
  ≡ @comm_ring_freyd_hom_class R A B e;
assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @computational_chain_pair_d (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain)
  ≡ @comm_ring_freyd_hom_class R B D d;
assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) ⊢
  @freyd_raw_chain_zero_path R A B D e d chain
  : τ (@= (@CommRingFreydHomSet R A D)
      (@comp_fapp0 (@CommRingFreydPresentation_cat R) A B D
        (@comm_ring_freyd_hom_class R B D d)
        (@comm_ring_freyd_hom_class R A B e))
      (@comm_ring_freyd_zero_class R A D));

assert [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) ⊢
  @fapp0 _ _ (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
    (@freyd_raw_chain_zero_cone R W P A B D e d chain)
  ≡ A;

// Merely possessing a raw agreement does not supply whole coherent kernels.
assertnot [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  (W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))) ⊢
  chain : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W);

/* This is an actual whole H at the raw native input, not an equality witness. */
type λ R : τ CommRing,
  λ T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)),
  λ W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)),
  λ V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)),
  λ P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W),
  λ Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) T0 V),
  λ A : τ (@CommRingPresentation R), λ B : τ (@CommRingPresentation R), λ D : τ (@CommRingPresentation R),
  λ e : τ (@CommRingPresentationMorphism R A B), λ d : τ (@CommRingPresentationMorphism R B D),
  λ chain : τ (@CommRingFreydChainPair R A B D e d),
  @fapp0 _ _ (@freyd_zero_cone_homology_func R T0 W V P Q)
    (@freyd_raw_chain_zero_cone R W P A B D e d chain);
