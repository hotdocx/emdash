/* The correction has zero target image and retains the original source class. */
require open emdash.emdash3_2_homology_map_corrections;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
    D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1))
  (H0 : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1))
  (z : τ (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0
    H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
    p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T))
  (a : τ (Hom C A0 A1)) (boundary_path : τ (@= (Hom C A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))
    (@comp_fapp0 C A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) z (@homology_record_boundary C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0))
    (@comp_fapp0 C A0 A1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_boundary C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) a))) ⊢
  @homology_map_corrected_cycle_zero C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a boundary_path
  : τ (@= (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1 p1 H1)) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
    D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A1 B1 D1 p1 H1) z (@homology_map_corrected_cycle C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)));

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
    D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1))
  (H0 : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1))
  (z : τ (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0
    H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
    p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T))
  (a : τ (Hom C A0 A1)) ⊢
  @homology_map_corrected_cycle_source_path C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a
  : τ (@= (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)) (@comp_fapp0 C
    (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0
    H0) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 p0 H0) (@homology_map_corrected_cycle C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) T
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
        p0 H0) (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z
        hf T test a) (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T
        (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_map_correction_step C P t Ab
        A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))));

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
    D0))
  (p1 : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1))
  (H0 : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0))
  (H1 : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1))
  (z : τ (Hom C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))) (hf : τ (@HomPrecompFactor C (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0
    H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
    p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T))
  (a : τ (Hom C A0 A1)) (a_epic : τ (@IsEpic C A0 A1 a)) ⊢
  @homology_map_correction_is_epic C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a a_epic
  : τ (@IsEpic C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) T (@comp_fapp0 C
    (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_object C P t
    Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
    test) (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)));
