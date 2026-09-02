/*
  Witness-rich exactness and short exact triples.

  Exactness at B for A --i--> B --p--> D is epicity of the selected lift
  A -> Ker(p). A short exact triple additionally retains monicity of i and
  epicity of p. No image/kernel object equality, manual diagram, rule, or
  unification clause is introduced.
*/

require open emdash.emdash3_2_computational_homology;
require open emdash.emdash3_2_abelian_categories;

symbol ComputationalExactAt
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : Grpd
≔ @IsEpic C A
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_homology_boundary C P t Abl A B D pair H);

symbol computational_exact_at_selected
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  : Grpd
≔ @ComputationalExactAt C P t Abl A B D pair
    (@computational_homology_at C P t Abl A B D pair);

symbol ComputationalShortExactTriple
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  : Grpd
≔ @Product_grpd
    (@IsMonic C A B
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t Abl) A B D pair))
    (@Product_grpd
      (@IsEpic C B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair))
      (@computational_exact_at_selected C P t Abl A B D pair));

symbol computational_short_exact_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (monic : τ (@IsMonic C A B
    (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t Abl) A B D pair)))
  (epic : τ (@IsEpic C B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)))
  (exact : τ (@computational_exact_at_selected C P t Abl A B D pair))
  : τ (@ComputationalShortExactTriple C P t Abl A B D pair)
≔ @Product_pair_grpd _ _ monic (@Product_pair_grpd _ _ epic exact);

symbol computational_short_exact_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  : τ (@IsMonic C A B
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t Abl) A B D pair))
≔ sigma_Fst S;

symbol computational_short_exact_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  : τ (@IsEpic C B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair))
≔ sigma_Fst (sigma_Snd S);

symbol computational_short_exact_at
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  : τ (@computational_exact_at_selected C P t Abl A B D pair)
≔ sigma_Snd (sigma_Snd S);

// The exactness witness concerns the actual selected boundary lift.
symbol computational_short_exact_boundary_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (S : τ (@ComputationalShortExactTriple C P t Abl A B D pair))
  : τ (@IsEpic C A
      (@computational_homology_cycle_object C P t Abl A B D pair
        (@computational_homology_at C P t Abl A B D pair))
      (@computational_homology_boundary C P t Abl A B D pair
        (@computational_homology_at C P t Abl A B D pair)))
≔ @computational_short_exact_at C P t Abl A B D pair S;
