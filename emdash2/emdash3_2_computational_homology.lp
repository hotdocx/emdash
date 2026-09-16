/*
  One-degree computational homology in a selected pre-Abelian category.

  A chain pair packages dNext : A -> B and d : B -> D with the ordinary
  annihilation path d o dNext = 0. The selected kernel of d is the cycle
  object. Kernel universality lifts dNext to the boundary map into cycles, and
  the selected cokernel of that boundary is homology. All data are projections
  of existing universal constructions; no image equality, manual diagram,
  rewrite rule, or unification rule is introduced.
*/

require open emdash.emdash3_2_homology_records;

// Read the preadditive structure already owned by one selected pre-Abelian value.
symbol computational_homology_preadditive
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  : τ (@PreadditiveCategory C)
≔ @additive_preadditive C P t (@preabelian_additive C P t Abl);

// The original kernel/lift/cokernel recipe also constructs this record.
symbol homology_record_selected [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S)) (V : τ (@HasComputationalCokernels C S))
  (A B D : τ (Obj C)) (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@HomologyRecord C S A B D pair)
≔ @homology_record_intro C S A B D pair (W B D (@computational_chain_pair_d C S A B D pair))
    (@is_contr_center _ (@computational_kernel_factor_contr C S B D
      (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair)) A (@computational_chain_pair_cone C S A B D pair)))
    (V A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair))) (@computational_kernel_lift C S B D (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair)) A (@computational_chain_pair_cone C S A B D pair)));

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
