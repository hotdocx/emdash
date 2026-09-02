/* Reviewer-facing one-degree computational homology consumers. */

require open emdash.emdash3_2_computational_homology;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C))
  (dNext : τ (Hom C A B))
  (d : τ (Hom C B D))
  (chain : τ (@= (Hom C A D)
    (@comp_fapp0 C A B D d dNext)
    (@preadditive_hom_zero C S A D)))
  ⊢ @computational_chain_pair_intro C S A B D dNext d chain
  : τ (@ComputationalChainPair C S A B D);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C))
  (dNext : τ (Hom C A B))
  (d : τ (Hom C B D))
  (chain : τ (@= (Hom C A D)
    (@comp_fapp0 C A B D d dNext)
    (@preadditive_hom_zero C S A D)))
  ⊢ @computational_chain_pair_dnext C S A B D
      (@computational_chain_pair_intro C S A B D dNext d chain)
  ≡ dNext;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C))
  (dNext : τ (Hom C A B))
  (d : τ (Hom C B D))
  (chain : τ (@= (Hom C A D)
    (@comp_fapp0 C A B D d dNext)
    (@preadditive_hom_zero C S A D)))
  ⊢ @computational_chain_pair_d C S A B D
      (@computational_chain_pair_intro C S A B D dNext d chain)
  ≡ d;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  ⊢ @computational_homology_at C P t Abl A B D pair
  : τ (@ComputationalHomologyAt C P t Abl A B D pair);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  ⊢ @computational_homology_boundary_path C P t Abl A B D pair H
  : τ (@= (Hom C A B)
      (@comp_fapp0 C A
        (@computational_homology_cycle_object C P t Abl A B D pair H) B
        (@computational_homology_cycle_embedding C P t Abl A B D pair H)
        (@computational_homology_boundary C P t Abl A B D pair H))
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t Abl) A B D pair));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  ⊢ @computational_homology_projection_path C P t Abl A B D pair H
  : τ (@= (Hom C A
      (@computational_homology_object C P t Abl A B D pair H))
      (@comp_fapp0 C A
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@computational_homology_object C P t Abl A B D pair H)
        (@computational_homology_projection C P t Abl A B D pair H)
        (@computational_homology_boundary C P t Abl A B D pair H))
      (@preadditive_hom_zero C
        (@computational_homology_preadditive C P t Abl) A
        (@computational_homology_object C P t Abl A B D pair H)));
