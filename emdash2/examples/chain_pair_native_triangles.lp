/* Original zero triangle, with no new filler or chain condition. */
require open emdash.emdash3_2_chain_pair_native_triangles;

// The third vertex is retained.
assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  sigma_Fst (sigma_Fst (@computational_chain_pair_native_zero_triangle C S A B D pair))
  ≡ D;

// The long edge is the same selected zero.
assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  sigma_Snd (sigma_Fst (@computational_chain_pair_native_zero_triangle C S A B D pair))
  ≡ @preadditive_hom_zero C S A D;

// The second differential is unchanged.
assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  sigma_Fst (sigma_Snd (@computational_chain_pair_native_zero_triangle C S A B D pair))
  ≡ @computational_chain_pair_d C S A B D pair;

// The native filler is the image of the original chain path.
assert
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  sigma_Snd (sigma_Snd (@computational_chain_pair_native_zero_triangle C S A B D pair))
  ≡ @path_to_hom (Hom_cat C A D)
      (@comp_fapp0 C A B D
        (@computational_chain_pair_d C S A B D pair)
        (@computational_chain_pair_dnext C S A B D pair))
      (@preadditive_hom_zero C S A D)
      (@computational_chain_pair_path C S A B D pair);

// A different initial differential is not silently substituted into the flag.
assertnot
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  (other : τ (Hom C A B)) ⊢
  @computational_chain_pair_native_zero_triangle C S A B D pair
  : τ (Obj (@DependentSimplex2_cat C A
      (@dependent_simplex1 C A B other)));
