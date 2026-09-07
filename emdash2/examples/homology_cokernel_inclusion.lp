/* Actual homology endpoints, reconstruction, and monic cancellation. */
require open emdash.emdash3_2_abelian_homology_cokernel_inclusion;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  ⊢
    (@computational_homology_cokernel_inclusion C P t PA A B D pair H) : τ (Hom C
      (@computational_homology_object C P t PA A B D pair H)
      (@computational_cokernel_object C
        (@computational_homology_preadditive C P t PA) A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t PA) A B D pair)
        (@computational_homology_dnext_cokernel C P t PA A B D pair)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  ⊢ @computational_homology_cokernel_inclusion_path C P t PA A B D pair H
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
          (@computational_homology_cycle_embedding C P t PA A B D pair H)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  ⊢
    (@computational_homology_cokernel_inclusion C P t PA A B D pair H) ≡ @cokernel_composite_comparison C
    (@computational_homology_preadditive C P t PA) A
    (@computational_homology_cycle_object C P t PA A B D pair H) B
    (@computational_homology_boundary C P t PA A B D pair H)
    (@computational_homology_cycle_embedding C P t PA A B D pair H)
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t PA) A B D pair)
    (@computational_homology_boundary_path C P t PA A B D pair H)
    (@computational_homology_cokernel C P t PA A B D pair H)
    (@computational_homology_dnext_cokernel C P t PA A B D pair);

assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A B D))
  (H : τ (@ComputationalHomologyAt C P t PA A B D pair))
  (other : τ (@ComputationalHomologyAt C P t PA A B D pair))
  ⊢ (@computational_homology_cokernel_inclusion C P t PA A B D pair H)
  : τ (Hom C
      (@computational_homology_object C P t PA A B D pair other)
      (@computational_cokernel_object C
        (@computational_homology_preadditive C P t PA) A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t PA) A B D pair)
        (@computational_homology_dnext_cokernel C P t PA A B D pair)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ
      (@ComputationalChainPair C
        (@computational_homology_preadditive C P t
          (@abelian_stability_preabelian C P t Ab)) A B D))
  (H : τ (@ComputationalHomologyAt C P t (@abelian_stability_preabelian C P t Ab) A B D pair))
  ⊢ @abelian_homology_cokernel_inclusion_monic C P t Ab A B D pair H
  : τ
    (@IsMonic C
      (@computational_homology_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_cokernel_object C
        (@computational_homology_preadditive C P t
          (@abelian_stability_preabelian C P t Ab)) A B
        (@computational_chain_pair_dnext C
          (@computational_homology_preadditive C P t
            (@abelian_stability_preabelian C P t Ab)) A B D pair)
        (@computational_homology_dnext_cokernel C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair))
      (@computational_homology_cokernel_inclusion C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ
      (@ComputationalChainPair C
        (@computational_homology_preadditive C P t
          (@abelian_stability_preabelian C P t Ab)) A B D))
  (H : τ (@ComputationalHomologyAt C P t (@abelian_stability_preabelian C P t Ab) A B D pair))
  (T : τ (Obj C))
  (u v : τ (Hom C T (@computational_homology_object C P t (@abelian_stability_preabelian C P t Ab) A B D pair H)))
  (equal : τ
      (@= (Hom C T
          (@computational_cokernel_object C
            (@computational_homology_preadditive C P t
              (@abelian_stability_preabelian C P t Ab)) A B
            (@computational_chain_pair_dnext C
              (@computational_homology_preadditive C P t
                (@abelian_stability_preabelian C P t Ab)) A B D pair)
            (@computational_homology_dnext_cokernel C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair)))
    (@comp_fapp0 C T
        (@computational_homology_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_cokernel_object C
          (@computational_homology_preadditive C P t
            (@abelian_stability_preabelian C P t Ab)) A B
          (@computational_chain_pair_dnext C
            (@computational_homology_preadditive C P t
              (@abelian_stability_preabelian C P t Ab)) A B D pair)
          (@computational_homology_dnext_cokernel C P t
            (@abelian_stability_preabelian C P t Ab) A B D pair))
        (@computational_homology_cokernel_inclusion C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H) u)
    (@comp_fapp0 C T
        (@computational_homology_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_cokernel_object C
          (@computational_homology_preadditive C P t
            (@abelian_stability_preabelian C P t Ab)) A B
          (@computational_chain_pair_dnext C
            (@computational_homology_preadditive C P t
              (@abelian_stability_preabelian C P t Ab)) A B D pair)
          (@computational_homology_dnext_cokernel C P t
            (@abelian_stability_preabelian C P t Ab) A B D pair))
        (@computational_homology_cokernel_inclusion C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H) v)))
  ⊢ (@abelian_homology_cokernel_inclusion_monic C P t Ab A B D pair H)
      T u v equal
  : τ
    (@= (Hom C T
        (@computational_homology_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)) u v);
