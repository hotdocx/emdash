/* Ordinary raw zero-composition input and its unchanged projections.
   This data view is shared by CAS adapters and retained ordinary records.
   It selects no universal object and does not replace native comma inputs,
   internal Hom owners or whole homology. */
require open emdash.emdash3_2_preadditive_categories;

// One composable zero pair A --dNext--> B --d--> D.
symbol ComputationalChainPair
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  (A B D : τ (Obj C))
  : Grpd
≔ `Σ_ dNext : τ (Hom C A B),
   `Σ_ d : τ (Hom C B D),
      @= (Hom C A D)
        (@comp_fapp0 C A B D d dNext)
        (@preadditive_hom_zero C S A D);

symbol computational_chain_pair_intro
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (dNext : τ (Hom C A B))
  (d : τ (Hom C B D))
  (chain : τ (@= (Hom C A D)
    (@comp_fapp0 C A B D d dNext)
    (@preadditive_hom_zero C S A D)))
  : τ (@ComputationalChainPair C S A B D)
≔ @Struct_sigma
    (Hom C A B)
    (λ dNext0 : τ (Hom C A B),
      `Σ_ d0 : τ (Hom C B D),
        @= (Hom C A D)
          (@comp_fapp0 C A B D d0 dNext0)
          (@preadditive_hom_zero C S A D))
    dNext
    (@Struct_sigma
      (Hom C B D)
      (λ d0 : τ (Hom C B D),
        @= (Hom C A D)
          (@comp_fapp0 C A B D d0 dNext)
          (@preadditive_hom_zero C S A D))
      d chain);

symbol computational_chain_pair_dnext
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Hom C A B)
≔ sigma_Fst pair;

symbol computational_chain_pair_d
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Hom C B D)
≔ sigma_Fst (sigma_Snd pair);

symbol computational_chain_pair_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (Hom C A D)
      (@comp_fapp0 C A B D
        (@computational_chain_pair_d C S A B D pair)
        (@computational_chain_pair_dnext C S A B D pair))
      (@preadditive_hom_zero C S A D))
≔ sigma_Snd (sigma_Snd pair);
