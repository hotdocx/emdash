/* The existing equality-valued chain pair in the native dependent triangle.
   This is a compatibility map into a fixed-flag simplex, not a declaration
   of a global category of complexes or a converse from arbitrary 2-cells. */
require open emdash.emdash3_2_computational_homology;
require open emdash.emdash3_2_dependent_simplex_native_dimensions;

// The long edge is the original zero; its filler uses the original chain path.
symbol computational_chain_pair_native_zero_triangle
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Obj (@DependentSimplex2_cat C A
      (@dependent_simplex1 C A B
        (@computational_chain_pair_dnext C S A B D pair))))
≔ @dependent_simplex2_visible C A B D
    (@computational_chain_pair_dnext C S A B D pair)
    (@preadditive_hom_zero C S A D)
    (@computational_chain_pair_d C S A B D pair)
    (@path_to_hom (Hom_cat C A D)
      (@comp_fapp0 C A B D
        (@computational_chain_pair_d C S A B D pair)
        (@computational_chain_pair_dnext C S A B D pair))
      (@preadditive_hom_zero C S A D)
      (@computational_chain_pair_path C S A B D pair));
