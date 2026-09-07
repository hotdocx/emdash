/*
  Laws of cycle maps, inherited from maps on the actual whole kernels.
  The data projections of chain-map identity/composition expose precisely
  the generic Hom-factor identity/pasting operations.
*/
require open emdash.emdash3_2_homology_cycle_maps;
require open emdash.emdash3_2_kernel_map_laws;
require open emdash.emdash3_2_chain_pair_map_composition;

symbol computational_homology_cycles_identity_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  : τ
    (@= (Hom C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0))
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A0 B0 D0 p0 p0 H0 H0
        (@computational_chain_pair_map_identity C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 p0))
      (@id C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)))
≔ @computational_kernel_map_identity_path C
  (@computational_homology_preadditive C P t PA) B0 D0
  (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
  (@computational_homology_cycles C P t PA A0 B0 D0 p0 H0);

symbol computational_homology_cycles_equal_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  (equal : τ
      (@= (Hom C B0 B1)
        (@computational_chain_pair_map_middle C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
        (@computational_chain_pair_map_middle C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 G)))
  : τ
    (@= (Hom C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1))
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 G))
≔ @computational_kernel_map_equal_path C (@computational_homology_preadditive C P t PA) B0 D0 B1 D1
    (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t PA) A1 B1 D1 p1)
      (@computational_homology_cycles C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_cycles C P t PA A1 B1 D1 p1 H1)
    (@computational_chain_pair_map_middle C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
      (@computational_chain_pair_map_middle C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 G)
      (@computational_chain_pair_map_lower C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
      (@computational_chain_pair_map_lower C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 G) equal;

symbol computational_homology_cycles_composition_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A2 B2 D2))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (H2 : τ (@ComputationalHomologyAt C P t PA A2 B2 D2 p2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A1 B1 D1 A2 B2 D2 p1 p2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ
    (@= (Hom C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A2 B2 D2 p2 H2))
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A2 B2 D2 p0 p2 H0 H2
          (@computational_chain_pair_map_comp C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_cycle_object C P t PA A2 B2 D2 p2 H2)
          (@computational_homology_cycles_map C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G)
          (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)))
≔ @computational_kernel_map_composition_path C (@computational_homology_preadditive C P t PA) B0 D0 B1 D1
    (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t PA) A1 B1 D1 p1)
      (@computational_homology_cycles C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_cycles C P t PA A1 B1 D1 p1 H1) B2 D2
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t PA) A2 B2 D2 p2)
      (@computational_homology_cycles C P t PA A2 B2 D2 p2 H2)
    (@computational_chain_pair_map_middle C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
      (@computational_chain_pair_map_middle C
        (@computational_homology_preadditive C P t PA) A1 B1 D1 A2 B2 D2 p1 p2 G)
      (@computational_chain_pair_map_lower C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
      (@computational_chain_pair_map_lower C
        (@computational_homology_preadditive C P t PA) A1 B1 D1 A2 B2 D2 p1 p2 G);
