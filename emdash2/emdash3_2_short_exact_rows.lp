/* A whole short exact row retains one pair and its dependent evidence. */

require open emdash.emdash3_2_short_exact_sequences;

symbol ComputationalShortExactRow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  : Grpd
≔ `Σ_ pair : τ (@ComputationalChainPair C
      (@computational_homology_preadditive C P t PA) A B D),
        (@ComputationalShortExactTriple C P t PA A B D pair);

symbol computational_short_exact_row_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
      (@computational_homology_preadditive C P t PA) A B D))
  (short : τ (@ComputationalShortExactTriple C P t PA A B D pair))
  : τ (@ComputationalShortExactRow C P t PA A B D)
≔ @Struct_sigma (@ComputationalChainPair C
      (@computational_homology_preadditive C P t PA) A B D)
    (λ pair : τ (@ComputationalChainPair C
      (@computational_homology_preadditive C P t PA) A B D),
        (@ComputationalShortExactTriple C P t PA A B D pair)) pair short;

symbol computational_short_exact_row_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t PA A B D))
  : τ (@ComputationalChainPair C
      (@computational_homology_preadditive C P t PA) A B D)
≔ sigma_Fst row;

symbol computational_short_exact_row_evidence
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t PA A B D))
  : τ (@ComputationalShortExactTriple C P t PA A B D
    (@computational_short_exact_row_pair C P t PA A B D row))
≔ sigma_Snd row;
