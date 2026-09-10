/*
  Boundary correction after an epimorphic incoming component.
  A further pullback lifts the target boundary without choosing a section.
  Subtract the actual source boundary in the source cycle object. Boundary
  naturality proves zero target image; its source homology class is unchanged.
*/
require open emdash.emdash3_2_homology_map_kernel_covers;
require open emdash.emdash3_2_preadditive_difference_paths;

symbol homology_map_correction_cover [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1))
  : τ (@ComputationalFiberProduct C P t (@abelian_stability_additive C P t Ab) (@homology_map_kernel_cover_object C P t Ab A0 B0 D0
    A1 B1 D1 p0 p1 H0 H1 z hf T test) A1 A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    a)
≔ @abelian_selected_fiber_product C P t Ab (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1
  A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) a;

symbol homology_map_correction_object [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1)) : τ (Obj C)
≔ @computational_fiber_product_object C P t (@abelian_stability_additive C P t Ab) (@homology_map_kernel_cover_object C P t Ab A0 B0
  D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1 A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
  test) a (@homology_map_correction_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a);

symbol homology_map_correction_step [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1)) : τ (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
≔ @computational_fiber_product_proj1 C P t (@abelian_stability_additive C P t Ab) (@homology_map_kernel_cover_object C P t Ab A0 B0
  D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1 A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
  test) a (@homology_map_correction_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a);

symbol homology_map_correction_incoming [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1)) : τ (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) A0)
≔ @computational_fiber_product_proj2 C P t (@abelian_stability_additive C P t Ab) (@homology_map_kernel_cover_object C P t Ab A0 B0
  D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1 A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
  test) a (@homology_map_correction_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a);

symbol homology_map_correction_step_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1))
  (a_epic : τ (@IsEpic C A0 A1 a))
  : τ (@IsEpic C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_map_correction_step C P t Ab
    A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))
≔ @abelian_fiber_product_epic_projection C P t Ab (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
  test) A1 A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) a a_epic;

symbol homology_map_correction_cover_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1))
  : τ (@= (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) A1)
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1
        (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_map_correction_step C P
        t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) A0 A1 a
        (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)))
≔ @computational_fiber_product_compatibility_path C P t (@abelian_stability_additive C P t Ab) (@homology_map_kernel_cover_object C
  P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1 A0 (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0
  H1 z hf T test) a (@homology_map_correction_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a);

// Subtract an actual source boundary in the source cycle object.
symbol homology_map_corrected_cycle [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1)) : τ (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
    D0 p0 H0))
≔ (@preadditive_hom_add C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_object C P t Ab
  A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1
  H0 H1 z hf T test) (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)) (@preadditive_hom_neg C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_map_correction_object C P t Ab
  A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1
  B1 D1 p0 p1 H0 H1 z hf T test a) A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_boundary C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0
  p1 H0 H1 z hf T test a))));

symbol homology_map_correction_image_path
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) a)))
  : τ (@= (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1 p1 H1))
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A1 B1 D1 p1 H1) z (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
        test a) (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
        (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)))
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A1 B1 D1 p1 H1) z (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
        test a) A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
        P t Ab)) A0 B0 D0 p0 H0) (@homology_record_boundary C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1
        p0 p1 H0 H1 z hf T test a))))
≔ @eq_trans _ _ _ _
    (@hom_factor_paste_path C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) A0
      (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1 (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
      B1 D1 p1 H1)
      (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_boundary
        C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) z (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1
        z hf T test a) (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) a
        (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
        D1 p1 H1)
      (@homology_map_correction_cover_path C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
      (@eq_sym _ _ _ (@homology_map_kernel_cover_target_path C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)) (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1
        B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))
        (λ h : τ (Hom C A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)), @comp_fapp0 C (@homology_map_correction_object C P t Ab A0
          B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) h (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1
          D1 p0 p1 H0 H1 z hf T test a)) _ _
        (@eq_sym _ _ _ boundary_path))
      (@eq_sym _ _ _ (@comp_assoc C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) A0
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A1 B1 D1 p1 H1) z (@homology_record_boundary C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1
        p0 p1 H0 H1 z hf T test a))));

symbol homology_map_corrected_cycle_zero
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) a)))
  : τ (@= (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1 p1 H1))
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A1 B1 D1 p1 H1) z (@homology_map_corrected_cycle C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)))
≔ @preadditive_difference_postcomp_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  p1 H1) z (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
  (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
  (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_map_correction_step C P t Ab A0
  B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1
  z hf T test a) A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) A0 B0 D0 p0 H0) (@homology_record_boundary C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0 p1
  H0 H1 z hf T test a)) (@homology_map_correction_image_path C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a boundary_path);

symbol homology_map_corrected_cycle_source_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1))
  : τ (@= (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0))
      (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_corrected_cycle C P t Ab A0 B0 D0 A1 B1 D1 p0
        p1 H0 H1 z hf T test a))
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
        A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))))
≔ @preadditive_postcompose_difference_right_zero_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test
  a) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
  D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
  B0 D0 p0 H0)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
      p0 H0) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
      (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_map_correction_step C P t Ab
      A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1
      H0 H1 z hf T test a) A0 (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_boundary C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)) (@comp_fapp0 C
      (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) T (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
      p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
      B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test) (@comp_fapp0 C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
      test a) (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T
      (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_map_correction_step C P t Ab A0
      B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))) (@hom_factor_paste_path C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1
      D1 p0 p1 H0 H1 z hf T test a) (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
      (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
      p0 H0)
      (@id C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)) (@homology_map_kernel_cover_epi
        C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_projection C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0
        p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@comp_fapp0
        C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_object
        C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1
        z hf T test) (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a))
        (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
        p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)
      (@eq_refl (Hom C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) T) (@comp_fapp0 C
        (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_object C
        P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z
        hf T test) (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)))
      (@homology_map_kernel_cover_source_path C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
        (@homology_record_boundary_factor_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0 (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
      (@homology_record_boundary_multiple C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A0 B0 D0 p0 H0 (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
        (@homology_map_correction_incoming C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)));

symbol homology_map_correction_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  (a : τ (Hom C A0 A1))
  (a_epic : τ (@IsEpic C A0 A1 a))
  : τ (@IsEpic C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) T (@comp_fapp0 C
    (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_object C P t
    Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
    test) (@homology_map_correction_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)))
≔ @is_epic_comp C (@homology_map_correction_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a)
  (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T (@homology_map_correction_step C P t Ab
  A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a) (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    (@homology_map_correction_step_is_epic C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test a a_epic)
    (@homology_map_kernel_cover_is_epic C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test);
