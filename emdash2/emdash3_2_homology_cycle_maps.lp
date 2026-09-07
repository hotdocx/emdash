/*
  Cycle maps and derived boundary compatibility for actual whole homologies.

  The lower Hom factor feeds the generic kernel map. The upper factor and
  the original boundary reconstructions imply compatibility by monicity of
  the actual target kernel embedding.
*/
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_kernel_maps;
require open emdash.emdash3_2_abelian_categories;

// The lower factor induces a map of the actual cycle kernels.
symbol computational_homology_cycles_map
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
  : τ (Hom C
      (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
      (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1))
≔ @computational_kernel_map C
  (@computational_homology_preadditive C P t PA) B0 D0 B1 D1
  (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
  (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t PA) A1 B1 D1 p1)
  (@computational_homology_cycles C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_cycles C P t PA A1 B1 D1 p1 H1)
  (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
  (@computational_chain_pair_map_lower C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F);

// Its kernel reconstruction.
symbol computational_homology_cycles_map_path
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
          (@computational_homology_cycle_embedding C P t PA A0 B0 D0 p0 H0)))
≔ @computational_kernel_map_path C
  (@computational_homology_preadditive C P t PA) B0 D0 B1 D1
  (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 p0)
  (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t PA) A1 B1 D1 p1)
  (@computational_homology_cycles C P t PA A0 B0 D0 p0 H0)
  (@computational_homology_cycles C P t PA A1 B1 D1 p1 H1)
  (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
  (@computational_chain_pair_map_lower C
    (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F);

// Compare the boundary maps after the actual target-cycle embedding.
symbol computational_homology_map_boundary_after_embedding
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
  : τ (@= (Hom C A0 B1)
      (@comp_fapp0 C A0
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) B1
          (@computational_homology_cycle_embedding C P t PA A1 B1 D1 p1 H1)
          (@comp_fapp0 C A0
            (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
            (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
            (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
            (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)))
      (@comp_fapp0 C A0
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) B1
          (@computational_homology_cycle_embedding C P t PA A1 B1 D1 p1 H1)
          (@comp_fapp0 C A0 A1
            (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
            (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
            (@computational_chain_pair_map_next C
              (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F))))
≔ (@eq_trans _ _ _ _
      (@comp_assoc C A0
          (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
          (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) B1
          (@computational_homology_cycle_embedding C P t PA A1 B1 D1 p1 H1)
          (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
          (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) B1) (Hom C A0 B1)
        (λ h : τ (Hom C
              (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) B1), @comp_fapp0 C A0
            (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) B1 h
            (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)) _ _
          (@computational_homology_cycles_map_path C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F))
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C A0
            (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0) B0 B1
            (@computational_chain_pair_map_middle C
              (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
            (@computational_homology_cycle_embedding C P t PA A0 B0 D0 p0 H0)
            (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A0 B0) (Hom C A0 B1)
        (λ h : τ (Hom C A0 B0), @comp_fapp0 C A0 B0 B1
            (@computational_chain_pair_map_middle C
              (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F) h) _ _
          (@computational_homology_boundary_path C P t PA A0 B0 D0 p0 H0))
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@computational_chain_pair_map_upper_path C
            (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A1 B1) (Hom C A0 B1)
        (λ h : τ (Hom C A1 B1), @comp_fapp0 C A0 A1 B1 h
            (@computational_chain_pair_map_next C
              (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)) _ _
          (@eq_sym _ _ _
            (@computational_homology_boundary_path C P t PA A1 B1 D1 p1 H1)))
      (@eq_sym _ _ _
          (@comp_assoc C A0 A1
            (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) B1
            (@computational_homology_cycle_embedding C P t PA A1 B1 D1 p1 H1)
            (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
            (@computational_chain_pair_map_next C
              (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)))))))));

// Cancel that kernel embedding; no boundary compatibility is postulated.
symbol computational_homology_map_boundary_path
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
          (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)))
≔
  (@computational_kernel_morphism_is_monic C
    (@computational_homology_preadditive C P t PA) B1 D1
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t PA) A1 B1 D1 p1)
    (@computational_homology_cycles C P t PA A1 B1 D1 p1 H1))
    A0
      (@comp_fapp0 C A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0))
      (@comp_fapp0 C A0 A1
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
        (@computational_chain_pair_map_next C
          (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F))
    (@computational_homology_map_boundary_after_embedding C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F);

// The derived compatibility is an ordinary internal postcomposition factor.
symbol computational_homology_map_boundary_factor
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
  : τ
    (@HomPostcompFactor C A1
      (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) A0
      (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
      (@comp_fapp0 C A0
        (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
        (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
        (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
        (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0)))
≔ @hom_postcomp_factor_intro C A1
  (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1) A0
  (@computational_homology_boundary C P t PA A1 B1 D1 p1 H1)
  (@comp_fapp0 C A0
    (@computational_homology_cycle_object C P t PA A0 B0 D0 p0 H0)
    (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 H1)
    (@computational_homology_cycles_map C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F)
    (@computational_homology_boundary C P t PA A0 B0 D0 p0 H0))
    (@computational_chain_pair_map_next C
        (@computational_homology_preadditive C P t PA) A0 B0 D0 A1 B1 D1 p0 p1 F)
      (@eq_sym _ _ _
        (@computational_homology_map_boundary_path C P t PA A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 F));
