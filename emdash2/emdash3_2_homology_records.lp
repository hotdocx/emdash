/* Ordinary observations of an actual boundary and its retained universal data.
   Whole K/Q consumers derive these records at the same chosen objects.
   This owner stores and projects supplied data; the W/V selection recipe stays
   downstream in the explicit ordinary reference implementation. */
require open emdash.emdash3_2_chain_pair_kernel_tests;
require open emdash.emdash3_2_kernels_cokernels;

symbol HomologyRecord [C : Cat] (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C)) (pair : τ (@ComputationalChainPair C S A B D)) : Grpd
≔ @Σ_ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair))
    (λ cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)),
      @Σ_ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair)
        (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles)
        (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles)
        A (@computational_chain_pair_cone C S A B D pair))
      (λ boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair)
        (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles)
        (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles)
        A (@computational_chain_pair_cone C S A B D pair)),
        @ComputationalCokernel C S A
          (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles)
          (sigma_Fst boundary)));

// Shared constructor: the boundary is the supplied internal factor point.
symbol homology_record_intro [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] [pair : τ (@ComputationalChainPair C S A B D)]
  (cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair))) (boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)))
  (cokernel : τ (@ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary)))
  : τ (@HomologyRecord C S A B D pair)
≔ @Struct_sigma (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair))
    (λ cycles : τ (@ComputationalKernel C S B D (@computational_chain_pair_d C S A B D pair)), @Σ_ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair))
      (λ boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)), @ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary)))
    cycles
    (@Struct_sigma (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair))
      (λ boundary : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair) (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (@computational_kernel_morphism C S B D (@computational_chain_pair_d C S A B D pair) cycles) A (@computational_chain_pair_cone C S A B D pair)), @ComputationalCokernel C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) cycles) (sigma_Fst boundary))
      boundary cokernel);

// Projections of the same actual-boundary record; no ambient PA package is needed.
// The retained universal kernel of the outgoing differential.
symbol homology_record_cycles
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@ComputationalKernel C S B D
      (@computational_chain_pair_d C S A B D pair))
≔ sigma_Fst H;

// Z: the retained cycle object.
symbol homology_record_cycle_object
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (Obj C)
≔ @computational_kernel_object C S B D
    (@computational_chain_pair_d C S A B D pair)
    (@homology_record_cycles C S A B D pair H);

// κ: Z → B, the retained kernel inclusion.
symbol homology_record_cycle_embedding
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (Hom C (@homology_record_cycle_object C S A B D pair H) B)
≔ @computational_kernel_morphism C S B D
    (@computational_chain_pair_d C S A B D pair)
    (@homology_record_cycles C S A B D pair H);

// The actual β together with its reconstruction in the existing factor fibre.
symbol homology_record_boundary_factor
  [C : Cat] [S : τ (@PreadditiveCategory C)] [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@KernelFactorSpace C S B D
    (@computational_chain_pair_d C S A B D pair)
    (@homology_record_cycle_object C S A B D pair H)
    (@homology_record_cycle_embedding C S A B D pair H)
    A (@computational_chain_pair_cone C S A B D pair))
≔ sigma_Fst (sigma_Snd H);

// β: A → Z; do not replace it by another expression for its unique factor.
symbol homology_record_boundary
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (Hom C A
      (@homology_record_cycle_object C S A B D pair H))
≔ sigma_Fst (@homology_record_boundary_factor C S A B D pair H);

// κ ∘ β = dNext, read from that same factor.
symbol homology_record_boundary_path
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@= (Hom C A B)
      (@comp_fapp0 C A
        (@homology_record_cycle_object C S A B D pair H) B
        (@homology_record_cycle_embedding C S A B D pair H)
        (@homology_record_boundary C S A B D pair H))
      (@computational_chain_pair_dnext C S A B D pair))
≔ sigma_Snd (@homology_record_boundary_factor C S A B D pair H);

// The retained universal cokernel of the actual β.
symbol homology_record_cokernel
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@ComputationalCokernel C S A
      (@homology_record_cycle_object C S A B D pair H)
      (@homology_record_boundary C S A B D pair H))
≔ sigma_Snd (sigma_Snd H);

// H: the retained quotient object.
symbol homology_record_object
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (Obj C)
≔ @computational_cokernel_object C S A
    (@homology_record_cycle_object C S A B D pair H)
    (@homology_record_boundary C S A B D pair H)
    (@homology_record_cokernel C S A B D pair H);

// q: Z → H, the retained cokernel projection.
symbol homology_record_projection
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (Hom C
      (@homology_record_cycle_object C S A B D pair H)
      (@homology_record_object C S A B D pair H))
≔ @computational_cokernel_morphism C S A
    (@homology_record_cycle_object C S A B D pair H)
    (@homology_record_boundary C S A B D pair H)
    (@homology_record_cokernel C S A B D pair H);

// q ∘ β = 0, from the retained cokernel's annihilation law.
symbol homology_record_projection_path
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C S A B D)]
  (H : τ (@HomologyRecord C S A B D pair))
  : τ (@= (Hom C A
      (@homology_record_object C S A B D pair H))
      (@comp_fapp0 C A
        (@homology_record_cycle_object C S A B D pair H)
        (@homology_record_object C S A B D pair H)
        (@homology_record_projection C S A B D pair H)
        (@homology_record_boundary C S A B D pair H))
      (@preadditive_hom_zero C S A
        (@homology_record_object C S A B D pair H)))
≔ @computational_cokernel_annihilation C S A
    (@homology_record_cycle_object C S A B D pair H)
    (@homology_record_boundary C S A B D pair H)
    (@homology_record_cokernel C S A B D pair H);

// Whole selected cycles/boundary/homology snapshot for one chain pair.
