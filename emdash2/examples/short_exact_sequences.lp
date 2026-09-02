/* Reviewer-facing witness-rich exactness and short exact triples. */

require open emdash.emdash3_2_short_exact_sequences;

// Exactness is cancellation for the selected boundary-to-kernel lift.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  ⊢ @ComputationalExactAt C P t Abl A B D pair H
  ≡ @IsEpic C A
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_homology_boundary C P t Abl A B D pair H);

// A short exact package exposes all three independent witnesses.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  ⊢ @computational_short_exact_monic C P t Abl A B D pair S
  : τ (@IsMonic C A B
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
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  ⊢ @computational_short_exact_epic C P t Abl A B D pair S
  : τ (@IsEpic C B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Abl : τ (@PreAbelianCategory C P t))
  (A B D : τ (Obj C))
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  ⊢ @computational_short_exact_boundary_epic C P t Abl A B D pair S
  : τ (@IsEpic C A
      (@computational_homology_cycle_object C P t Abl A B D pair
        (@computational_homology_at C P t Abl A B D pair))
      (@computational_homology_boundary C P t Abl A B D pair
        (@computational_homology_at C P t Abl A B D pair)));
