/* The two native boundary squares of the existing chain-pair map.
   Both squares use the same middle component of the original factor package;
   no independently supplied commuting-square data are introduced. */
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_hom_factor_cubical;

// upper: the existing postcomposition factor, in native cubical Hom.
symbol computational_chain_pair_map_upper_square
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Obj (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 (@computational_chain_pair_dnext C S A0 B0 D0 p0))
        (@lax_edge C A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1))))
≔ @hom_postcomp_factor_square C A0 B0 A1 B1
    (@computational_chain_pair_dnext C S A0 B0 D0 p0)
    (@computational_chain_pair_dnext C S A1 B1 D1 p1)
    (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
    (@computational_chain_pair_map_upper C S A0 B0 D0 A1 B1 D1 p0 p1 F);

// lower: the existing precomposition factor, in native cubical Hom.
symbol computational_chain_pair_map_lower_square
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Obj (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@lax_edge C B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1))))
≔ @hom_precomp_factor_square C B0 D0 B1 D1
    (@computational_chain_pair_d C S A0 B0 D0 p0)
    (@computational_chain_pair_d C S A1 B1 D1 p1)
    (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F)
    (@computational_chain_pair_map_lower C S A0 B0 D0 A1 B1 D1 p0 p1 F);

// A whole fixed-pair comparison into the two native boundary Homs.
// Its image shares the original middle map. The ambient product also contains
// incompatible pairs; it is not being declared the category of chain maps.
symbol computational_chain_pair_map_cubical_boundary_func
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor
      (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
      (Product_cat
        (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 (@computational_chain_pair_dnext C S A0 B0 D0 p0))
        (@lax_edge C A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1)))
        (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@lax_edge C B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1)))))
≔ @fapp0 _ _
    (@path_lift_func
      (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)
      (Product_cat
        (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C A0 B0 (@computational_chain_pair_dnext C S A0 B0 D0 p0))
        (@lax_edge C A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1)))
        (Hom_cat (@LaxArrow_cat C)
        (@lax_edge C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0))
        (@lax_edge C B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1)))))
    (λ F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1),
      Struct_sigma
        (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 F));
