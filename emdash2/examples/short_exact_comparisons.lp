/* The endpoint isomorphisms retain their actual universal factors. */

require open emdash.emdash3_2_short_exact_cokernel_comparison;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ @iso_evidence_to C A (@computational_homology_cycle_object C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
    (@short_exact_kernel_comparison_iso C P t Ab A B D pair short)
  ≡ (@short_exact_kernel_comparison C P t Ab A B D pair);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ @computational_homology_boundary_path C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair)
  : τ (@= (Hom C A B)
      (@comp_fapp0 C _ _ _ (@computational_homology_cycle_embedding C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair)) (@iso_evidence_to C A
        (@computational_homology_cycle_object C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair))
        (@short_exact_kernel_comparison_iso C P t Ab A B D pair short)))
      (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ @iso_evidence_to C (@short_exact_cokernel_object C P t Ab A B D pair) D
    (@short_exact_cokernel_comparison_iso C P t Ab A B D pair short)
  ≡ (@short_exact_cokernel_comparison C P t Ab A B D pair);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ @iso_evidence_from C (@short_exact_cokernel_object C P t Ab A B D pair) D
    (@short_exact_cokernel_comparison_iso C P t Ab A B D pair short)
  ≡ (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ @short_exact_cokernel_comparison_path C P t Ab A B D pair
  : τ (@= (Hom C B D)
      (@comp_fapp0 C _ _ _ (@iso_evidence_to C (@short_exact_cokernel_object C P t Ab A B D pair) D
        (@short_exact_cokernel_comparison_iso C P t Ab A B D pair short))
        (@short_exact_cokernel_projection C P t Ab A B D pair)) (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ @short_exact_cokernel_comparison_inverse_path C P t Ab A B D pair short
  : τ (@= (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair))
      (@comp_fapp0 C _ _ _ (@iso_evidence_from C
        (@short_exact_cokernel_object C P t Ab A B D pair) D
        (@short_exact_cokernel_comparison_iso C P t Ab A B D pair short))
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair))
        (@short_exact_cokernel_projection C P t Ab A B D pair));

// A symbolic inverse comparison is not a section of the original epimorphism.
assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  ⊢ (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short)
  : τ (Hom C D B);
