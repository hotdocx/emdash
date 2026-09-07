/*
  Identity, extensionality, and composition of generic induced homology maps.

  First compare the cycle maps by kernel uniqueness. Then use cokernel-map
  extensionality/composition on the original boundary cokernels.
*/
require open emdash.emdash3_2_homology_maps;
require open emdash.emdash3_2_homology_cycle_map_laws;
require open emdash.emdash3_2_cokernel_map_laws;

symbol computational_homology_map_identity_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  : τ
    (@= (Hom C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0))
      (@computational_homology_map C P t PA A0 B0 D0 A0 B0 D0 p0 p0 H0 H0
        (@computational_chain_pair_map_identity C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 p0))
      (@id C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)))
≔ @eq_trans _ _ _ _
    (@computational_cokernel_map_equal_path C
        (@computational_homology_preadditive C P t PA) A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A0 B0 D0 p0 p0 H0 H0
          (@computational_chain_pair_map_identity C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 p0))
        (@id C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0))
        (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A0 B0 D0 p0 p0 H0 H0
          (@computational_chain_pair_map_identity C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 p0))
        (@hom_postcomp_factor_identity C A0
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0))
      (@computational_homology_cycles_identity_path C P t PA A0 B0 D0 p0 H0))
    (@computational_cokernel_map_identity_path C
        (@computational_homology_preadditive C P t PA) A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0));

symbol computational_homology_map_equal_path
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
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
      (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
      (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 G))
≔ @computational_cokernel_map_equal_path C
  (@computational_homology_preadditive C P t PA) A0
  (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
  (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
      (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_cokernel C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 G)
      (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
      (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 G)
    (@computational_homology_cycles_equal_path C P t PA
      A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F G equal);

symbol computational_homology_map_composition_path
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
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A2 B2 D2 p2 H2))
      (@computational_homology_map C P t PA A0 B0 D0 A2 B2 D2 p0 p2 H0 H2
          (@computational_chain_pair_map_comp C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F))
      (@comp_fapp0 C
          (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_object C P t PA A2 B2 D2 p2 H2)
          (@computational_homology_map C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G)
          (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)))
≔ @eq_trans _ _ _ _
    (@computational_cokernel_map_equal_path C
        (@computational_homology_preadditive C P t PA) A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A2
        (@computational_homology_cycle_object C P t PA A2 B2 D2 p2 H2)
      (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_boundary C P t PA A2 B2 D2 p2 H2)
        (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cokernel C P t PA A2 B2 D2 p2 H2)
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A2 B2 D2 p0 p2 H0 H2
          (@computational_chain_pair_map_comp C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F))
        (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_cycle_object C P t PA A2 B2 D2 p2 H2)
          (@computational_homology_cycles_map C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G)
          (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F))
        (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A2 B2 D2 p0 p2 H0 H2
          (@computational_chain_pair_map_comp C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 G F))
        (@hom_postcomp_factor_paste C A0
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) A2
          (@computational_homology_cycle_object C P t PA A2 B2 D2 p2 H2)
      (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_boundary C P t PA A2 B2 D2 p2 H2)
        (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_cycles_map C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G)
        (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_map_boundary_factor C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G))
      (@computational_homology_cycles_composition_path C P t PA
        A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 H0 H1 H2 G F))
    (@computational_cokernel_map_composition_path C
        (@computational_homology_preadditive C P t PA) A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
      (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cokernel C P t PA A1 B1 D1 p1 H1) A2
        (@computational_homology_cycle_object C P t PA A2 B2 D2 p2 H2)
        (@computational_homology_boundary C P t PA A2 B2 D2 p2 H2)
        (@computational_homology_cokernel C P t PA A2 B2 D2 p2 H2)
      (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_cycles_map C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G)
        (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_map_boundary_factor C P t PA A1 B1 D1 A2 B2 D2 p1 p2 H1 H2 G));
