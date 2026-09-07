/* The source of a short exact row is canonically isomorphic to Ker(p). */

require open emdash.emdash3_2_mono_epi_comparisons;
require open emdash.emdash3_2_short_exact_sequences;
require open emdash.emdash3_2_abelian_bimorphisms;

// The comparison is the existing selected boundary into cycles.
symbol short_exact_kernel_comparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (Hom C A (@computational_homology_cycle_object C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair)))
≔ (@computational_homology_boundary C P t (@computational_abelian_preabelian C P t Ab) A B D pair
  (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair));

// Monicity of i descends to its factor e through the selected kernel embedding.
symbol short_exact_kernel_comparison_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@IsMonic C A (@computational_homology_cycle_object C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
    (@short_exact_kernel_comparison C P t Ab A B D pair))
≔ @is_monic_of_monic_factor C A (@computational_homology_cycle_object C P t
  (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
  (@computational_abelian_preabelian C P t Ab) A B D pair)) B
    (@short_exact_kernel_comparison C P t Ab A B D pair)
      (@computational_homology_cycle_embedding C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair)) (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@computational_homology_boundary_path C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair))
    (@computational_short_exact_monic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short);

// Exactness supplies epicity of that same boundary; balancedness constructs its inverse.
symbol short_exact_kernel_comparison_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@IsoEvidence C A (@computational_homology_cycle_object C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair)))
≔ @computational_abelian_bimorphism_iso C P t Ab A (@computational_homology_cycle_object C P t
  (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
  (@computational_abelian_preabelian C P t Ab) A B D pair))
    (@short_exact_kernel_comparison C P t Ab A B D pair)
    (@short_exact_kernel_comparison_monic C P t Ab A B D pair short)
    (@computational_short_exact_boundary_epic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short);
