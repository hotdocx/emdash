/* The outgoing arrow descends through the selected cokernel of i. */

require open emdash.emdash3_2_short_exact_kernel_comparison;

symbol short_exact_incoming_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (@ComputationalCokernel C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair))
≔ @preabelian_cokernel C P t (@computational_abelian_preabelian C P t Ab) A B
  (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair);

symbol short_exact_cokernel_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (Obj C)
≔ @computational_cokernel_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
  (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair)
  (@short_exact_incoming_cokernel C P t Ab A B D pair);

symbol short_exact_cokernel_projection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair))
≔ @computational_cokernel_morphism C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
  (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair)
  (@short_exact_incoming_cokernel C P t Ab A B D pair);

symbol short_exact_cokernel_comparison_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (@CokernelCoannihilator C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair) D)
≔ @Struct_sigma (Hom C B D)
    (λ h : τ (Hom C B D), @= (Hom C A D)
      (@comp_fapp0 C _ _ _ h (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A D))
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@computational_chain_pair_path C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair);

symbol short_exact_cokernel_comparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (Hom C (@short_exact_cokernel_object C P t Ab A B D pair) D)
≔ @computational_cokernel_colift C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
  (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair)
  (@short_exact_incoming_cokernel C P t Ab A B D pair) D
    (@short_exact_cokernel_comparison_cocone C P t Ab A B D pair);

symbol short_exact_cokernel_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (@= (Hom C B D)
      (@comp_fapp0 C _ _ _ (@short_exact_cokernel_comparison C P t Ab A B D pair)
        (@short_exact_cokernel_projection C P t Ab A B D pair)) (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair))
≔ @computational_cokernel_colift_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
  (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair)
  (@short_exact_incoming_cokernel C P t Ab A B D pair) D
    (@short_exact_cokernel_comparison_cocone C P t Ab A B D pair);
