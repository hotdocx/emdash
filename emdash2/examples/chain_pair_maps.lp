/* Chain-pair map data are inherited factor points with ordinary projections. */
require open emdash.emdash3_2_chain_pair_map_composition;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (next : τ (Hom C A0 A1))
  (middle : τ (Hom C B0 B1))
  (prev : τ (Hom C D0 D1))
  (upper : τ
      (@= (Hom C A0 B1)
        (@comp_fapp0 C A0 A1 B1
          (@computational_chain_pair_dnext C S A1 B1 D1 p1) next)
        (@comp_fapp0 C A0 B0 B1 middle
          (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ
      (@= (Hom C B0 D1)
        (@comp_fapp0 C B0 D0 D1 prev
          (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1) middle)))
  ⊢ @computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1
    (@computational_chain_pair_map_of_components C S A0 B0 D0 A1 B1 D1 p0 p1 next middle prev upper lower) ≡ next;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (next : τ (Hom C A0 A1))
  (middle : τ (Hom C B0 B1))
  (prev : τ (Hom C D0 D1))
  (upper : τ
      (@= (Hom C A0 B1)
        (@comp_fapp0 C A0 A1 B1
          (@computational_chain_pair_dnext C S A1 B1 D1 p1) next)
        (@comp_fapp0 C A0 B0 B1 middle
          (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ
      (@= (Hom C B0 D1)
        (@comp_fapp0 C B0 D0 D1 prev
          (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1) middle)))
  ⊢ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1
    (@computational_chain_pair_map_of_components C S A0 B0 D0 A1 B1 D1 p0 p1 next middle prev upper lower) ≡ middle;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (next : τ (Hom C A0 A1))
  (middle : τ (Hom C B0 B1))
  (prev : τ (Hom C D0 D1))
  (upper : τ
      (@= (Hom C A0 B1)
        (@comp_fapp0 C A0 A1 B1
          (@computational_chain_pair_dnext C S A1 B1 D1 p1) next)
        (@comp_fapp0 C A0 B0 B1 middle
          (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ
      (@= (Hom C B0 D1)
        (@comp_fapp0 C B0 D0 D1 prev
          (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1) middle)))
  ⊢ @computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1
    (@computational_chain_pair_map_of_components C S A0 B0 D0 A1 B1 D1 p0 p1 next middle prev upper lower) ≡ prev;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (next : τ (Hom C A0 A1))
  (middle : τ (Hom C B0 B1))
  (prev : τ (Hom C D0 D1))
  (upper : τ
      (@= (Hom C A0 B1)
        (@comp_fapp0 C A0 A1 B1
          (@computational_chain_pair_dnext C S A1 B1 D1 p1) next)
        (@comp_fapp0 C A0 B0 B1 middle
          (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ
      (@= (Hom C B0 D1)
        (@comp_fapp0 C B0 D0 D1 prev
          (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1) middle)))
  ⊢ @computational_chain_pair_map_upper_path C S A0 B0 D0 A1 B1 D1 p0 p1
    (@computational_chain_pair_map_of_components C S A0 B0 D0 A1 B1 D1 p0 p1 next middle prev upper lower) ≡ upper;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (next : τ (Hom C A0 A1))
  (middle : τ (Hom C B0 B1))
  (prev : τ (Hom C D0 D1))
  (upper : τ
      (@= (Hom C A0 B1)
        (@comp_fapp0 C A0 A1 B1
          (@computational_chain_pair_dnext C S A1 B1 D1 p1) next)
        (@comp_fapp0 C A0 B0 B1 middle
          (@computational_chain_pair_dnext C S A0 B0 D0 p0))))
  (lower : τ
      (@= (Hom C B0 D1)
        (@comp_fapp0 C B0 D0 D1 prev
          (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@comp_fapp0 C B0 B1 D1
          (@computational_chain_pair_d C S A1 B1 D1 p1) middle)))
  ⊢ @computational_chain_pair_map_lower_path C S A0 B0 D0 A1 B1 D1 p0 p1
    (@computational_chain_pair_map_of_components C S A0 B0 D0 A1 B1 D1 p0 p1 next middle prev upper lower) ≡ lower;

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 : τ (Obj C)) (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  ⊢ @computational_chain_pair_map_next C S A0 B0 D0 A0 B0 D0 p0 p0
      (@computational_chain_pair_map_identity C S A0 B0 D0 p0)
  ≡ @id C A0;

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 : τ (Obj C)) (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  ⊢ @computational_chain_pair_map_middle C S A0 B0 D0 A0 B0 D0 p0 p0
      (@computational_chain_pair_map_identity C S A0 B0 D0 p0)
  ≡ @id C B0;

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 : τ (Obj C)) (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  ⊢ @computational_chain_pair_map_prev C S A0 B0 D0 A0 B0 D0 p0 p0
      (@computational_chain_pair_map_identity C S A0 B0 D0 p0)
  ≡ @id C D0;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C S A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 p1 p2))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_chain_pair_map_next C S A0 B0 D0 A2 B2 D2 p0 p2
    (@computational_chain_pair_map_comp C S A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F)
  ≡ @comp_fapp0 C A0 A1 A2
      (@computational_chain_pair_map_next C S A1 B1 D1 A2 B2 D2 p1 p2 G)
      (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 F);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C S A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 p1 p2))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_chain_pair_map_middle C S A0 B0 D0 A2 B2 D2 p0 p2
    (@computational_chain_pair_map_comp C S A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F)
  ≡ @comp_fapp0 C B0 B1 B2
      (@computational_chain_pair_map_middle C S A1 B1 D1 A2 B2 D2 p1 p2 G)
      (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C S A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 p1 p2))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_chain_pair_map_prev C S A0 B0 D0 A2 B2 D2 p0 p2
    (@computational_chain_pair_map_comp C S A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F)
  ≡ @comp_fapp0 C D0 D1 D2
      (@computational_chain_pair_map_prev C S A1 B1 D1 A2 B2 D2 p1 p2 G)
      (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F);

assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C S A2 B2 D2))
  (other : τ (@ComputationalChainPair C S A1 B1 D1))
  (G : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 other p2))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢
    (@computational_chain_pair_map_comp C S A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F) : τ
    (@ComputationalChainPairMap C S A0 B0 D0 A2 B2 D2 p0 p2);

// Different proofs of the same adjacent-zero equation do not obstruct map data.
assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C)) (a : τ (Hom C A B)) (b : τ (Hom C B D))
  (p q : τ (@= (Hom C A D) (@comp_fapp0 C A B D b a) (@preadditive_hom_zero C S A D)))
  ⊢ @computational_chain_pair_map_identity C S A B D (@computational_chain_pair_intro C S A B D a b p)
  : τ (@ComputationalChainPairMap C S A B D A B D
      (@computational_chain_pair_intro C S A B D a b p)
      (@computational_chain_pair_intro C S A B D a b q));
