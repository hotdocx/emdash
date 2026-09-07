/*
  A map between two chain pairs determines the existing snake triple.

  delta is the top incoming map, beta the middle component, and lambda the
  bottom outgoing map. The upper factor and bottom zero law derive the
  triple-zero point. No extra coherence input is required.
*/
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_abelian_snake_lemma;

symbol chain_pair_map_snake_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C A0 D1)
      (@comp_fapp0 C A0 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) (@comp_fapp0 C A0 B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@computational_chain_pair_dnext C S A0 B0 D0 p0)))
      (@preadditive_hom_zero C S A0 D1))
≔ (@eq_trans _ _ _ _
    (@eq_ap (Hom C A0 B1) (Hom C A0 D1)
      (λ h : τ (Hom C A0 B1), @comp_fapp0 C A0 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) h)
      _ _ (@eq_sym _ _ _ (@computational_chain_pair_map_upper_path C S A0 B0 D0 A1 B1 D1 p0 p1 F)))
    (@eq_trans _ _ _ _
      (@comp_assoc C A0 A1 B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1) (@computational_chain_pair_dnext C S A1 B1 D1 p1) (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 F))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C A1 D1) (Hom C A0 D1)
          (λ h : τ (Hom C A1 D1), @comp_fapp0 C A0 A1 D1 h (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 F))
          _ _ (@computational_chain_pair_path C S A1 B1 D1 p1))
        (@preadditive_comp_zero_left_path C S A0 A1 D1 (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 F)))));

// Short exactness is needed later for comparisons, not for this construction.
symbol chain_pair_map_snake_triple
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@AbelianSnakeTriple C S A0 B0 B1 D1)
≔ @abelian_snake_triple_intro C S A0 B0 B1 D1 (@computational_chain_pair_dnext C S A0 B0 D0 p0) (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@computational_chain_pair_d C S A1 B1 D1 p1)
    (@chain_pair_map_snake_zero_path C S A0 B0 D0 A1 B1 D1 p0 p1 F);
