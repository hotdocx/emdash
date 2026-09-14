/* Supplied model hypotheses; assertions check retained whole operations. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_adapter;
require open emdash.emdash3_2_commutative_algebra_freyd_native_inputs;

symbol R : τ CommRing;
symbol Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R));
symbol P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R));
symbol P2 : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R));
symbol Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@comm_ring_zero_presentation R) Z);
symbol M ≔ @freyd_adjunction_model_intro R Z P Q;

// The three supplied fields, with no ordinary W/V prerequisite.
assert ⊢ @freyd_adjunction_model_initial R M ≡ Z;
assert ⊢ @freyd_adjunction_model_kernels R M ≡ P;
assert ⊢ @freyd_adjunction_model_cokernels R M ≡ Q;
assertnot ⊢ @freyd_adjunction_model_kernels R M ≡ P2;
assert ⊢ @freyd_adjunction_model_func R M ≡
  @zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q;

// The legacy adapter retains the whole H functor and its complete Hom action.
symbol L : τ (FreydHomologyModel R);
symbol u : τ (Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)));
symbol v : τ (Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)));
assert ⊢ @freyd_adjunction_model_initial R (@freyd_homology_model_adjunctions R L)
  ≡ @freyd_homology_model_initial R L;
assert ⊢ @freyd_adjunction_model_func R (@freyd_homology_model_adjunctions R L)
  ≡ @freyd_homology_model_func R L;
assert ⊢ @fapp1_func _ _ (@freyd_adjunction_model_func R (@freyd_homology_model_adjunctions R L)) u v
  ≡ @fapp1_func _ _ (@freyd_homology_model_func R L) u v;

symbol S2 : τ (@CommRingPresentation R);
symbol S1 : τ (@CommRingPresentation R);
symbol S0 : τ (@CommRingPresentation R);
symbol e : τ (@CommRingPresentationMorphism R S2 S1);
symbol d : τ (@CommRingPresentationMorphism R S1 S0);
symbol chain : τ (@CommRingFreydChainPair R S2 S1 S0 e d);

// Original legacy input and its H point are not recentered or reselected.
assert ⊢ @fapp0 _ _ (@freyd_adjunction_model_func R (@freyd_homology_model_adjunctions R L))
    (@freyd_homology_model_input R L S2 S1 S0 e d chain)
  ≡ @freyd_homology_model_object R L S2 S1 S0 e d chain;

// Independent native input is also accepted, without W/V, model normality or a new square.
assert ⊢ @fapp0 _ _ (@freyd_adjunction_model_func R M)
  (@freyd_raw_chain_native_cone R S2 S1 S0 e d chain) : τ (@CommRingPresentation R);
