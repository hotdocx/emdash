/* The unchanged raw zero pair as an ordinary annihilator test.
   This view selects no kernel and depends on no homology algorithm. */
require open emdash.emdash3_2_chain_pair_data;
require open emdash.emdash3_2_weak_kernels;

// The chain pair read as the existing annihilator fibre of d.
symbol computational_chain_pair_cone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@WeakKernelAnnihilator C S B D
      (@computational_chain_pair_d C S A B D pair) A)
≔ @Struct_sigma
    (Hom C A B)
    (λ dNext : τ (Hom C A B),
      @= (Hom C A D)
        (@comp_fapp0 C A B D
          (@computational_chain_pair_d C S A B D pair) dNext)
        (@preadditive_hom_zero C S A D))
    (@computational_chain_pair_dnext C S A B D pair)
    (@computational_chain_pair_path C S A B D pair);
