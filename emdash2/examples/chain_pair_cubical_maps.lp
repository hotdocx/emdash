/* Native cubical comparison retains the original chain-map components. */
require open emdash.emdash3_2_chain_pair_cubical_maps;

assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0
      (@computational_chain_pair_dnext C S A0 B0 D0 p0))
    (@lax_edge C A1 B1
      (@computational_chain_pair_dnext C S A1 B1 D1 p1))
    (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F)
  ≡ @computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 F;

assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0
      (@computational_chain_pair_dnext C S A0 B0 D0 p0))
    (@lax_edge C A1 B1
      (@computational_chain_pair_dnext C S A1 B1 D1 p1))
    (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F)
  ≡ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F;

assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C B0 D0
      (@computational_chain_pair_d C S A0 B0 D0 p0))
    (@lax_edge C B1 D1
      (@computational_chain_pair_d C S A1 B1 D1 p1))
    (@computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 F)
  ≡ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 F;

assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C B0 D0
      (@computational_chain_pair_d C S A0 B0 D0 p0))
    (@lax_edge C B1 D1
      (@computational_chain_pair_d C S A1 B1 D1 p1))
    (@computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 F)
  ≡ @computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 p0 p1 F;

// The shared middle map is judgmentally the same, not glued by a new path.
assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0
      (@computational_chain_pair_dnext C S A0 B0 D0 p0))
    (@lax_edge C A1 B1
      (@computational_chain_pair_dnext C S A1 B1 D1 p1))
    (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F)
  ≡ @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C B0 D0
      (@computational_chain_pair_d C S A0 B0 D0 p0))
    (@lax_edge C B1 D1
      (@computational_chain_pair_d C S A1 B1 D1 p1))
    (@computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 F);

assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  sigma_Fst (@fapp0 _ _ (@computational_chain_pair_map_cubical_boundary_func C S A0 B0 D0 A1 B1 D1 p0 p1) F)
  ≡ @computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F;

assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  sigma_Snd (@fapp0 _ _ (@computational_chain_pair_map_cubical_boundary_func C S A0 B0 D0 A1 B1 D1 p0 p1) F)
  ≡ @computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 F;

// Distinct original middle maps are not identified by this comparison.
assertnot
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (G : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  sigma_Fst (sigma_Snd (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F))
  ≡ sigma_Fst (sigma_Snd (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 G));

// Iterated hom action remains available at the fixed-pair comparison.
assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (G : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_func _ _ (@computational_chain_pair_map_cubical_boundary_func C S A0 B0 D0 A1 B1 D1 p0 p1) F G
  : τ (Functor
      (Hom_cat (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) F G)
      (Hom_cat
        (Product_cat
          (Hom_cat (@LaxArrow_cat C)
            (@lax_edge C A0 B0 (@computational_chain_pair_dnext C S A0 B0 D0 p0))
            (@lax_edge C A1 B1 (@computational_chain_pair_dnext C S A1 B1 D1 p1)))
          (Hom_cat (@LaxArrow_cat C)
            (@lax_edge C B0 D0 (@computational_chain_pair_d C S A0 B0 D0 p0))
            (@lax_edge C B1 D1 (@computational_chain_pair_d C S A1 B1 D1 p1))))
        (Struct_sigma (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 F) (@computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 F))
        (Struct_sigma
          (@computational_chain_pair_map_upper_square C S A0 B0 D0 A1 B1 D1 p0 p1 G)
          (@computational_chain_pair_map_lower_square C S A0 B0 D0 A1 B1 D1 p0 p1 G))));
