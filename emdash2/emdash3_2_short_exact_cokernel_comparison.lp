/* Normal epi colifting constructs the inverse Coker(i) comparison. */

require open emdash.emdash3_2_short_exact_cokernel_inverse_test;
require open emdash.emdash3_2_mono_epi_comparisons;

symbol short_exact_cokernel_comparison_inverse
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (Hom C D (@short_exact_cokernel_object C P t Ab A B D pair))
≔ @colift_along_epimorphism C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@computational_abelian_epi_colifts C P t Ab)
    B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair)
      (@computational_short_exact_epic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short)
      (@short_exact_cokernel_object C P t Ab A B D pair)
      (@short_exact_cokernel_inverse_test C P t Ab A B D pair short);

symbol short_exact_cokernel_comparison_inverse_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@= (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair))
      (@comp_fapp0 C _ _ _ (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short)
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair))
        (@short_exact_cokernel_projection C P t Ab A B D pair))
≔ @colift_along_epimorphism_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@computational_abelian_epi_colifts C P t Ab)
    B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair)
      (@computational_short_exact_epic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short)
      (@short_exact_cokernel_object C P t Ab A B D pair)
      (@short_exact_cokernel_inverse_test C P t Ab A B D pair short);

// Both arrows are the selected universal factors; epic cancellation gives the laws.
symbol short_exact_cokernel_comparison_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@IsoEvidence C (@short_exact_cokernel_object C P t Ab A B D pair) D)
≔ @iso_from_epic_comparisons C B (@short_exact_cokernel_object C P t Ab A B D pair) D
    (@short_exact_cokernel_projection C P t Ab A B D pair) (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_cokernel_comparison C P t Ab A B D pair)
    (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short)
    (@computational_cokernel_morphism_is_epic C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair)
      (@short_exact_incoming_cokernel C P t Ab A B D pair))
    (@computational_short_exact_epic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short)
    (@short_exact_cokernel_comparison_path C P t Ab A B D pair)
    (@short_exact_cokernel_comparison_inverse_path C P t Ab A B D pair short);
