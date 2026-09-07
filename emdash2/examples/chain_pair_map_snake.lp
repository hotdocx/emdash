/* Row maps derive the snake triple and retain each actual component. */
require open emdash.emdash3_2_chain_pair_map_snake;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @abelian_snake_delta C S A0 B0 B1 D1 (@chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 p0 p1 F) ≡ (@computational_chain_pair_dnext C S A0 B0 D0 p0);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @abelian_snake_beta C S A0 B0 B1 D1 (@chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 p0 p1 F) ≡ (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @abelian_snake_lambda C S A0 B0 B1 D1 (@chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 p0 p1 F) ≡ (@computational_chain_pair_d C S A1 B1 D1 p1);

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @abelian_snake_zero_path C S A0 B0 B1 D1 (@chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 p0 p1 F) ≡ (@chain_pair_map_snake_zero_path C S A0 B0 D0 A1 B1 D1 p0 p1 F);

assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (other : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 other))
  ⊢ (@chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 p0 p1 F) : τ (@AbelianSnakeTriple C S A0 B0 B1 D1);
