/*
  Identity and composition of internal chain-pair maps.

  Compose the two existing Hom-fibre factors. Ordinary component and path
  observations are inherited from those factor operations.
*/
require open emdash.emdash3_2_chain_pair_maps;

symbol computational_chain_pair_map_identity
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  : τ (@ComputationalChainPairMap C S A0 B0 D0 A0 B0 D0 p0 p0)
≔ @computational_chain_pair_map_intro C S A0 B0 D0 A0 B0 D0 p0 p0 (@id C B0)
    (@hom_postcomp_factor_identity C A0 B0 (@computational_chain_pair_dnext C S A0 B0 D0 p0))
    (@hom_precomp_factor_identity C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0));

// G after F; their actual middle chain pair is shared by the input types.
symbol computational_chain_pair_map_comp
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C S A2 B2 D2))
  (G : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 p1 p2))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@ComputationalChainPairMap C S A0 B0 D0 A2 B2 D2 p0 p2)
≔ @computational_chain_pair_map_intro C S A0 B0 D0 A2 B2 D2 p0 p2
    (@comp_fapp0 C B0 B1 B2
        (@computational_chain_pair_map_middle C S A1 B1 D1 A2 B2 D2 p1 p2 G)
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F))
    (@hom_postcomp_factor_paste C A0 B0 A1 B1 A2 B2
      (@computational_chain_pair_dnext C S A0 B0 D0 p0)
        (@computational_chain_pair_dnext C S A1 B1 D1 p1)
        (@computational_chain_pair_dnext C S A2 B2 D2 p2)
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_map_middle C S A1 B1 D1 A2 B2 D2 p1 p2 G)
        (@computational_chain_pair_map_upper C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_map_upper C S A1 B1 D1 A2 B2 D2 p1 p2 G))
    (@hom_precomp_factor_paste C B0 D0 B1 D1 B2 D2
      (@computational_chain_pair_d C S A0 B0 D0 p0)
        (@computational_chain_pair_d C S A1 B1 D1 p1)
        (@computational_chain_pair_d C S A2 B2 D2 p2)
        (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_map_middle C S A1 B1 D1 A2 B2 D2 p1 p2 G)
        (@computational_chain_pair_map_lower C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_map_lower C S A1 B1 D1 A2 B2 D2 p1 p2 G));
