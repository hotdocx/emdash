/*
  One-degree computational homology in a selected pre-Abelian category.

  A chain pair packages dNext : A -> B and d : B -> D with the ordinary
  annihilation path d o dNext = 0. The selected kernel of d is the cycle
  object. Kernel universality lifts dNext to the boundary map into cycles, and
  the selected cokernel of that boundary is homology. All data are projections
  of existing universal constructions; no image equality, manual diagram,
  rewrite rule, or unification rule is introduced.
*/

require open emdash.emdash3_2_kernels_cokernels;

// One composable zero pair A --dNext--> B --d--> D.
symbol ComputationalChainPair
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C))
  : Grpd
≔ `Σ_ dNext : τ (Hom C A B),
   `Σ_ d : τ (Hom C B D),
      @= (Hom C A D)
        (@comp_fapp0 C A B D d dNext)
        (@preadditive_hom_zero C S A D);

symbol computational_chain_pair_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (dNext : τ (Hom C A B))
  (d : τ (Hom C B D))
  (chain : τ (@= (Hom C A D)
    (@comp_fapp0 C A B D d dNext)
    (@preadditive_hom_zero C S A D)))
  : τ (@ComputationalChainPair C S A B D)
≔ @Struct_sigma
    (Hom C A B)
    (λ dNext0 : τ (Hom C A B),
      `Σ_ d0 : τ (Hom C B D),
        @= (Hom C A D)
          (@comp_fapp0 C A B D d0 dNext0)
          (@preadditive_hom_zero C S A D))
    dNext
    (@Struct_sigma
      (Hom C B D)
      (λ d0 : τ (Hom C B D),
        @= (Hom C A D)
          (@comp_fapp0 C A B D d0 dNext)
          (@preadditive_hom_zero C S A D))
      d chain);

symbol computational_chain_pair_dnext
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Hom C A B)
≔ sigma_Fst pair;

symbol computational_chain_pair_d
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Hom C B D)
≔ sigma_Fst (sigma_Snd pair);

symbol computational_chain_pair_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (Hom C A D)
      (@comp_fapp0 C A B D
        (@computational_chain_pair_d C S A B D pair)
        (@computational_chain_pair_dnext C S A B D pair))
      (@preadditive_hom_zero C S A D))
≔ sigma_Snd (sigma_Snd pair);

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
