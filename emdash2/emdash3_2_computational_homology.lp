/*
  One-degree computational homology in a selected pre-Abelian category.

  A chain pair packages dNext : A -> B and d : B -> D with the ordinary
  annihilation path d o dNext = 0. The selected kernel of d is the cycle
  object. Kernel universality lifts dNext to the boundary map into cycles, and
  the selected cokernel of that boundary is homology. All data are projections
  of existing universal constructions; no image equality, manual diagram,
  rewrite rule, or unification rule is introduced.
*/

require open emdash.emdash3_2_chain_pair_data;
require open emdash.emdash3_2_kernels_cokernels;

// The chain pair read as the existing annihilator fibre of d.
symbol computational_chain_pair_cone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@WeakKernelAnnihilator C S B D
      (@computational_chain_pair_d C S A B D pair) A)
≔ @Struct_sigma
    (Hom C A B)
    (λ dNext : τ (Hom C A B),
      @= (Hom C A D)
        (@comp_fapp0 C A B D
          (@computational_chain_pair_d C S A B D pair) dNext)
        (@preadditive_hom_zero C S A D))
    (@computational_chain_pair_dnext C S A B D pair)
    (@computational_chain_pair_path C S A B D pair);

// Read the preadditive structure already owned by one selected pre-Abelian value.
symbol computational_homology_preadditive
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  : τ (@PreadditiveCategory C)
≔ @additive_preadditive C P t (@preabelian_additive C P t Abl);

// Actual-boundary records for whole K/Q/H. Operational fields are retained;
// the legacy canonical wrapper below remains unchanged during migration.
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

// The original kernel/lift/cokernel recipe also constructs this record.
symbol homology_record_selected [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (A B D : τ (Obj C)) (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@HomologyRecord C S A B D pair)
≔ @homology_record_intro C S A B D pair (W B D (@computational_chain_pair_d C S A B D pair))
    (@is_contr_center _ (@computational_kernel_factor_contr C S B D
      (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair)) A (@computational_chain_pair_cone C S A B D pair)))
    (V A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair))) (@computational_kernel_lift C S B D (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair)) A (@computational_chain_pair_cone C S A B D pair)));

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
symbol ComputationalHomologyAt
  [C : Cat]
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  : Grpd
≔ `Σ_ cycles : τ (@ComputationalKernel C
      (@computational_homology_preadditive C P t Abl) B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair)),
   @ComputationalCokernel C
      (@computational_homology_preadditive C P t Abl)
      A
      (@computational_kernel_object C
        (@computational_homology_preadditive C P t Abl) B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        cycles)
      (@computational_kernel_lift C
        (@computational_homology_preadditive C P t Abl) B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        cycles A
        (@computational_chain_pair_cone C
          (@computational_homology_preadditive C P t Abl) A B D pair));

symbol computational_homology_at
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  : τ (@ComputationalHomologyAt C P t Abl A B D pair)
≔ @Struct_sigma
    (@ComputationalKernel C
      (@computational_homology_preadditive C P t Abl) B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair))
    (λ cycles : τ (@ComputationalKernel C
        (@computational_homology_preadditive C P t Abl) B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)),
      @ComputationalCokernel C
        (@computational_homology_preadditive C P t Abl)
        A
        (@computational_kernel_object C
          (@computational_homology_preadditive C P t Abl) B D
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          cycles)
        (@computational_kernel_lift C
          (@computational_homology_preadditive C P t Abl) B D
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          cycles A
          (@computational_chain_pair_cone C
            (@computational_homology_preadditive C P t Abl) A B D pair)))
    ((@preabelian_kernels C P t Abl) B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair))
    ((@preabelian_cokernels C P t Abl) A
      (@computational_kernel_object C
        (@computational_homology_preadditive C P t Abl) B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        ((@preabelian_kernels C P t Abl) B D
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair)))
      (@computational_kernel_lift C
        (@computational_homology_preadditive C P t Abl) B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        ((@preabelian_kernels C P t Abl) B D
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair))
        A
        (@computational_chain_pair_cone C
          (@computational_homology_preadditive C P t Abl) A B D pair)));

symbol computational_homology_cycles
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (@ComputationalKernel C
      (@computational_homology_preadditive C P t Abl) B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair))
≔ sigma_Fst H;

symbol computational_homology_cycle_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@computational_homology_preadditive C P t Abl) B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    (@computational_homology_cycles C P t Abl A B D pair H);

symbol computational_homology_cycle_embedding
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (Hom C (@computational_homology_cycle_object C P t Abl A B D pair H) B)
≔ @computational_kernel_morphism C
    (@computational_homology_preadditive C P t Abl) B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    (@computational_homology_cycles C P t Abl A B D pair H);

symbol computational_homology_boundary
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (Hom C A
      (@computational_homology_cycle_object C P t Abl A B D pair H))
≔ @computational_kernel_lift C
    (@computational_homology_preadditive C P t Abl) B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    (@computational_homology_cycles C P t Abl A B D pair H)
    A
    (@computational_chain_pair_cone C
      (@computational_homology_preadditive C P t Abl) A B D pair);

symbol computational_homology_boundary_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (@= (Hom C A B)
      (@comp_fapp0 C A
        (@computational_homology_cycle_object C P t Abl A B D pair H) B
        (@computational_homology_cycle_embedding C P t Abl A B D pair H)
        (@computational_homology_boundary C P t Abl A B D pair H))
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t Abl) A B D pair))
≔ @computational_kernel_lift_path C
    (@computational_homology_preadditive C P t Abl) B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    (@computational_homology_cycles C P t Abl A B D pair H)
    A
    (@computational_chain_pair_cone C
      (@computational_homology_preadditive C P t Abl) A B D pair);

symbol computational_homology_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (@ComputationalCokernel C
      (@computational_homology_preadditive C P t Abl) A
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_homology_boundary C P t Abl A B D pair H))
≔ sigma_Snd H;

symbol computational_homology_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@computational_homology_preadditive C P t Abl) A
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_homology_boundary C P t Abl A B D pair H)
    (@computational_homology_cokernel C P t Abl A B D pair H);

symbol computational_homology_projection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (Hom C
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_homology_object C P t Abl A B D pair H))
≔ @computational_cokernel_morphism C
    (@computational_homology_preadditive C P t Abl) A
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_homology_boundary C P t Abl A B D pair H)
    (@computational_homology_cokernel C P t Abl A B D pair H);

symbol computational_homology_projection_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (@= (Hom C A
      (@computational_homology_object C P t Abl A B D pair H))
      (@comp_fapp0 C A
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@computational_homology_object C P t Abl A B D pair H)
        (@computational_homology_projection C P t Abl A B D pair H)
        (@computational_homology_boundary C P t Abl A B D pair H))
      (@preadditive_hom_zero C
        (@computational_homology_preadditive C P t Abl) A
        (@computational_homology_object C P t Abl A B D pair H)))
≔ @computational_cokernel_annihilation C
    (@computational_homology_preadditive C P t Abl) A
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_homology_boundary C P t Abl A B D pair H)
    (@computational_homology_cokernel C P t Abl A B D pair H);
