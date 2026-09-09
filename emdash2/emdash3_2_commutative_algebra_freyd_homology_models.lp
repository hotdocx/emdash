/* Explicit coherent model context; no automatic native/global provider. */
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cone_maps;

symbol FreydHomologyModel (R : τ CommRing) : Grpd
≔ `Σ_ Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)), `Σ_ W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), `Σ_ V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), @Product_grpd (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W) (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V);

symbol freyd_homology_model_intro [R : τ CommRing]
  (Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))) (W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))) (V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)))
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) (Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V))
  : τ (FreydHomologyModel R)
≔ @Struct_sigma (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)) (λ Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)), `Σ_ W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), `Σ_ V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), @Product_grpd (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W) (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V)) Z
    (@Struct_sigma (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)) (λ W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), `Σ_ V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), @Product_grpd (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W) (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V)) W
      (@Struct_sigma (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)) (λ V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)), @Product_grpd (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W) (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V)) V
        (@Product_pair_grpd (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W) (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V) P Q)));

symbol freyd_homology_model_initial [R : τ CommRing] (M : τ (FreydHomologyModel R))
  : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))
≔ sigma_Fst M;
symbol freyd_homology_model_kernels [R : τ CommRing] (M : τ (FreydHomologyModel R))
  : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))
≔ sigma_Fst (sigma_Snd M);
symbol freyd_homology_model_cokernels [R : τ CommRing] (M : τ (FreydHomologyModel R))
  : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))
≔ sigma_Fst (sigma_Snd (sigma_Snd M));
symbol freyd_homology_model_kernel_presentation [R : τ CommRing] (M : τ (FreydHomologyModel R))
  : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_homology_model_kernels R M))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd M)));
symbol freyd_homology_model_cokernel_presentation [R : τ CommRing] (M : τ (FreydHomologyModel R))
  : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@freyd_homology_model_initial R M) (@freyd_homology_model_cokernels R M))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd M)));

// The actual whole homology functor, not a new runtime owner.
symbol freyd_homology_model_func [R : τ CommRing] (M : τ (FreydHomologyModel R))
  : τ (Functor (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R))
≔ @freyd_zero_cone_homology_func R (@freyd_homology_model_initial R M) (@freyd_homology_model_kernels R M) (@freyd_homology_model_cokernels R M)
    (@freyd_homology_model_kernel_presentation R M) (@freyd_homology_model_cokernel_presentation R M);

symbol freyd_homology_model_input [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
≔ @freyd_raw_chain_zero_cone R (@freyd_homology_model_kernels R M) (@freyd_homology_model_kernel_presentation R M) A B D e d chain;

// A readable point observation, still defined by ordinary whole-H application.
symbol freyd_homology_model_object [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@CommRingPresentation R)
≔ @fapp0 _ _ (@freyd_homology_model_func R M)
    (@freyd_homology_model_input R M A B D e d chain);
