/* Given model data compute back to the same choices and whole H. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_models;

assert [R : τ CommRing] (Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))) (W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))) (V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)))
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) (Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V)) ⊢
  @freyd_homology_model_kernels R (@freyd_homology_model_intro R Z W V P Q) ≡ W;
assert [R : τ CommRing] (Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))) (W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))) (V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)))
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) (Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V)) ⊢
  @freyd_homology_model_func R (@freyd_homology_model_intro R Z W V P Q)
  ≡ @freyd_zero_cone_homology_func R Z W V P Q;
