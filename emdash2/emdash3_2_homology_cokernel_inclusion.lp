/*
  The canonical map from the actual homology to the incoming-differential
  cokernel. It is the existing cokernel-composite comparison at the selected
  cycles/boundary. Its monicity needs the Abelian specialization downstream.
*/
require open emdash.emdash3_2_computational_homology;
require open emdash.emdash3_2_cokernel_composite_comparison;

// Select Coker(dNext), without changing the existing homology object.
symbol computational_homology_dnext_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  : τ
    (@ComputationalCokernel C
      (@computational_homology_preadditive C P t PA) A B
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t PA) A B D pair))
≔
  (@preabelian_cokernels C P t PA) A B
  (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t PA) A B D pair);

// H(pair) → Coker(dNext), using the actual whole homology supplied.
symbol computational_homology_cokernel_inclusion
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  : τ (Hom C
      (@computational_homology_object C P t PA A B D pair H)
      (@computational_cokernel_object C
        (@computational_homology_preadditive C P t PA) A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t PA) A B D pair)
        (@computational_homology_dnext_cokernel C P t PA A B D pair)))
≔ @cokernel_composite_comparison C
  (@computational_homology_preadditive C P t PA) A
  (@computational_homology_cycle_object C P t PA A B D pair H) B
  (@computational_homology_boundary C P t PA A B D pair H)
  (@computational_homology_cycle_embedding C P t PA A B D pair H)
  (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t PA) A B D pair)
  (@computational_homology_boundary_path C P t PA A B D pair H)
  (@computational_homology_cokernel C P t PA A B D pair H)
  (@computational_homology_dnext_cokernel C P t PA A B D pair);

// Inclusion ∘ homology projection = ambient cokernel projection ∘ cycle embedding.
symbol computational_homology_cokernel_inclusion_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  : τ
    (@= (Hom C
        (@computational_homology_cycle_object C P t PA A B D pair H)
        (@computational_cokernel_object C
          (@computational_homology_preadditive C P t PA) A B
          (@computational_chain_pair_dnext C
            (@computational_homology_preadditive C P t PA) A B D pair)
          (@computational_homology_dnext_cokernel C P t PA A B D pair)))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A B D pair H)
          (@computational_homology_object C P t PA A B D pair H)
          (@computational_cokernel_object C
            (@computational_homology_preadditive C P t PA) A B
            (@computational_chain_pair_dnext C
              (@computational_homology_preadditive C P t PA) A B D pair)
            (@computational_homology_dnext_cokernel C P t PA A B D pair))
        (@computational_homology_cokernel_inclusion C P t PA A B D pair H)
        (@computational_homology_projection C P t PA A B D pair H))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A B D pair H) B
          (@computational_cokernel_object C
            (@computational_homology_preadditive C P t PA) A B
            (@computational_chain_pair_dnext C
              (@computational_homology_preadditive C P t PA) A B D pair)
            (@computational_homology_dnext_cokernel C P t PA A B D pair))
          (@computational_cokernel_morphism C
            (@computational_homology_preadditive C P t PA) A B
            (@computational_chain_pair_dnext C
              (@computational_homology_preadditive C P t PA) A B D pair)
            (@computational_homology_dnext_cokernel C P t PA A B D pair))
          (@computational_homology_cycle_embedding C P t PA A B D pair H)))
≔ @cokernel_composite_comparison_path C
  (@computational_homology_preadditive C P t PA) A
  (@computational_homology_cycle_object C P t PA A B D pair H) B
  (@computational_homology_boundary C P t PA A B D pair H)
  (@computational_homology_cycle_embedding C P t PA A B D pair H)
  (@computational_chain_pair_dnext C
    (@computational_homology_preadditive C P t PA) A B D pair)
  (@computational_homology_boundary_path C P t PA A B D pair H)
  (@computational_homology_cokernel C P t PA A B D pair H)
  (@computational_homology_dnext_cokernel C P t PA A B D pair);
