/*
  Inverse middle components give inverse maps on the actual chosen homologies.

  Extra component/factor choices do not affect the induced map: the equality
  theorem depends only on the middle arrow. No homology object is replaced.
*/
require open emdash.emdash3_2_homology_map_laws;
require open emdash.emdash3_2_iso_evidence_constructors;

symbol computational_homology_maps_inverse_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t PA) A1 B1 D1))
  (H0 : τ (@ComputationalHomologyAt C P t PA A0 B0 D0 p0))
  (H1 : τ (@ComputationalHomologyAt C P t PA A1 B1 D1 p1))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0))
  (inverse : τ
      (@= (Hom C B0 B0)
        (@comp_fapp0 C B0 B1 B0
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A1 B1 D1 A0 B0 D0 p1 p0 G)
          (@computational_chain_pair_map_middle C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F))
        (@id C B0)))
  : τ
    (@= (Hom C
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_object C P t PA A0 B0 D0 p0 H0))
      (@comp_fapp0 C
          (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_map C P t PA A1 B1 D1 A0 B0 D0 p1 p0 H1 H0 G)
          (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F))
      (@id C (@computational_homology_object C P t PA A0 B0 D0 p0 H0)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@computational_homology_map_composition_path C P t PA
        A0 B0 D0 A1 B1 D1 A0 B0 D0 p0 p1 p0 H0 H1 H0 G F))
    (@eq_trans _ _ _ _
      (@computational_homology_map_equal_path C P t PA
        A0 B0 D0 A0 B0 D0 p0 p0 H0 H0
          (@computational_chain_pair_map_comp C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 A0 B0 D0 p0 p1 p0 G F)
          (@computational_chain_pair_map_identity C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 p0) inverse)
      (@computational_homology_map_identity_path C P t PA A0 B0 D0 p0 H0));

symbol computational_homology_maps_iso
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
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
  : τ
    (@IsoEvidence C
      (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_object C P t PA A1 B1 D1 p1 H1))
≔ @iso_evidence_intro C
  (@computational_homology_object C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_object C P t PA A1 B1 D1 p1 H1)
  (@computational_homology_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
  (@computational_homology_map C P t PA A1 B1 D1 A0 B0 D0 p1 p0 H1 H0 G)
    (@computational_homology_maps_inverse_path C P t PA
      A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F G inverse0)
    (@computational_homology_maps_inverse_path C P t PA
      A1 B1 D1 A0 B0 D0 p1 p0 H1 H0 G F inverse1);
