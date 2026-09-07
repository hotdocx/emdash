/* Generic homology-map consumers at actual selected universal objects. */
require open emdash.emdash3_2_homology_map_isos;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢
    (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F) : τ (Hom C
      (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_object C P t PA A1 B1 D1 p1 H1));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢
    (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F) ≡ @computational_cokernel_map C
    (@computational_homology_preadditive C P t PA) A0
    (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) A1
    (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)
    (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_cokernel C P t PA A0 B0 D0 p0 H0)
    (@computational_homology_cokernel C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
    (@computational_homology_map_boundary_factor C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_homology_cycles_map_path C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F
  : τ (@= (Hom C (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) B1)
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) B1
          (@computational_homology_cycle_embedding C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) B0 B1
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
          (@computational_homology_cycle_embedding C P t PA A0 B0 D0 p0 H0)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_homology_map_boundary_path C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F
  : τ
    (@= (Hom C A0
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1))
      (@comp_fapp0 C A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0))
      (@comp_fapp0 C A0 A1
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
        (@computational_chain_pair_map_next C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_homology_map_path C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F
  : τ
    (@= (Hom C
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
          (@computational_homology_projection C P t PA A0 B0 D0 p0 H0))
      (@comp_fapp0 C
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_projection C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)));

assertnot
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  (other : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  ⊢
    (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F) : τ (Hom C
      (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_object C P t PA A1 B1 D1 p1 other));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  ⊢ @computational_homology_map_identity_path C P t PA A0 B0 D0 p0 H0
  : τ
    (@= (Hom C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0))
      (@computational_homology_map C P t PA A0 B0 D0 A0 B0 D0 p0 p0 H0 H0
          (@computational_chain_pair_map_identity C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 p0))
        (@id C
          (@computational_homology_object C P t PA A0 B0 D0 p0 H0)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (p2 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A2 B2 D2))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (H2 : τ (@ComputationalHomologyAt C P t PA A2 B2 D2 p2))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A1 B1 D1 A2 B2 D2 p1 p2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  ⊢ @computational_homology_map_composition_path C P t PA
      A0 B0 D0 A1 B1 D1 A2 B2 D2 p0 p1 p2 H0 H1 H2 G F
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
          (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
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
  ⊢ @computational_homology_map_equal_path C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F G equal
  : τ
    (@= (Hom C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
      (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 G));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0))
  (inverse0 : τ
      (@= (Hom C B0 B0)
        (@comp_fapp0 C B0 B1 B0
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0 G)
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F))
        (@id C B0)))
  (inverse1 : τ
      (@= (Hom C B1 B1)
        (@comp_fapp0 C B1 B0 B1
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0 G))
        (@id C B1)))
  ⊢ @iso_evidence_to C
    (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
    (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_maps_iso C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F G inverse0 inverse1) ≡
    (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F);

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 A1 B1 D1 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0))
  (inverse0 : τ
      (@= (Hom C B0 B0)
        (@comp_fapp0 C B0 B1 B0
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0 G)
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F))
        (@id C B0)))
  (inverse1 : τ
      (@= (Hom C B1 B1)
        (@comp_fapp0 C B1 B0 B1
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0 G))
        (@id C B1)))
  ⊢ @iso_evidence_from C
    (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
    (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_maps_iso C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F G inverse0 inverse1) ≡
    (@computational_homology_map C P t PA A1 B1 D1 A0 B0 D0 p1 p0 H1 H0 G);

// Different whole homology choices are compared by actual maps, not object paths.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (PA : τ (@PreAbelianCategory C P t))
  (A0 B0 D0 : τ (Obj C))
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (other : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  ⊢ @computational_homology_maps_iso C P t PA
      A0 B0 D0 A0 B0 D0 p0 p0 H0 other
        (@computational_chain_pair_map_identity C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
        (@computational_chain_pair_map_identity C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
      (@eq_refl (Hom C B0 B0) (@id C B0))
      (@eq_refl (Hom C B0 B0) (@id C B0))
  : τ
    (@IsoEvidence C
      (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_object C P t PA A0 B0 D0 p0 other));
