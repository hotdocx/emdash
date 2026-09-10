/* Actual-boundary records retain the supplied factors and original selections. */
require open emdash.emdash3_2_computational_homology;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_cycles C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ cycles;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_boundary_factor C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ boundary;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_boundary C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ sigma_Fst boundary;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_boundary_path C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ sigma_Snd boundary;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_cokernel C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ quotient;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_object C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ @computational_cokernel_object C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary) quotient;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_projection C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ @computational_cokernel_morphism C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary) quotient;

// A different supplied boundary is not silently replaced by this quotient's input.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary)))
  (other : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair))) ⊢
  @homology_record_intro C S A B D pair cycles other quotient
  : τ (@HomologyRecord C S A B D pair);

// Retain a supplied factor instead of forcing the selected contraction centre.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)))
  (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (quotient : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))) ⊢
  @homology_record_boundary C S A B D pair (@homology_record_intro C S A B D pair cycles boundary quotient)
  ≡ @computational_kernel_lift C S B D (@computational_chain_pair_d C S A B D pair) cycles A (@computational_chain_pair_cone C S A B D pair);

// The canonical recipe selects exactly the previous value.
assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D)) ⊢
  @homology_record_cycle_object C (@computational_homology_preadditive C P t PA) A B D pair (@homology_record_selected C (@computational_homology_preadditive C P t PA) (@preabelian_kernels C P t PA) (@preabelian_cokernels C P t PA) A B D pair)
  ≡ @computational_homology_cycle_object C P t PA A B D pair
      (@computational_homology_at C P t PA A B D pair);

// The canonical recipe selects exactly the previous value.
assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D)) ⊢
  @homology_record_boundary C (@computational_homology_preadditive C P t PA) A B D pair (@homology_record_selected C (@computational_homology_preadditive C P t PA) (@preabelian_kernels C P t PA) (@preabelian_cokernels C P t PA) A B D pair)
  ≡ @computational_homology_boundary C P t PA A B D pair
      (@computational_homology_at C P t PA A B D pair);

// The canonical recipe selects exactly the previous value.
assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D)) ⊢
  @homology_record_object C (@computational_homology_preadditive C P t PA) A B D pair (@homology_record_selected C (@computational_homology_preadditive C P t PA) (@preabelian_kernels C P t PA) (@preabelian_cokernels C P t PA) A B D pair)
  ≡ @computational_homology_object C P t PA A B D pair
      (@computational_homology_at C P t PA A B D pair);

// The record type ignores the chosen chain-zero proof when its two arrows agree.

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (incoming : τ (Hom C A B)) (outgoing : τ (Hom C B D))
  (z1 z2 : τ (@= (Hom C A D) (@comp_fapp0 C A B D outgoing incoming)
    (@preadditive_hom_zero C S A D))) ⊢
  @HomologyRecord C S A B D (@computational_chain_pair_intro C S A B D incoming outgoing z1)
  ≡ @HomologyRecord C S A B D (@computational_chain_pair_intro C S A B D incoming outgoing z2);
