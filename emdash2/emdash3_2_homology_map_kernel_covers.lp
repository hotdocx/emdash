/*
  Local lifting of an annihilated homology-map test.
  Pull the test back along the retained source quotient, then cover its
  target-boundary image. All maps and witnesses belong to the existing
  pullback/exact-cover records. No H object is reselected.
*/
require open emdash.emdash3_2_homology_record_cancellation;
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_cokernel_record_covers;

symbol homology_record_test_cover [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (T : τ (Obj C)) (u : τ (Hom C T (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H)))
  : τ (@ComputationalFiberProduct C P t (@abelian_stability_additive C P t Ab) T (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) u (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H))
≔ @abelian_selected_fiber_product C P t Ab T (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_cycle_object C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) u (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H);

symbol homology_record_test_cover_object [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (T : τ (Obj C)) (u : τ (Hom C T (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) : τ (Obj C)
≔ @computational_fiber_product_object C P t (@abelian_stability_additive C P t Ab) T (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) u (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A B D pair H) (@homology_record_test_cover C P t Ab A B D pair H T u);

symbol homology_record_test_cover_epi [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (T : τ (Obj C)) (u : τ (Hom C T (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) : τ (Hom C (@homology_record_test_cover_object C P t Ab A B D pair
    H T u) T)
≔ @computational_fiber_product_proj1 C P t (@abelian_stability_additive C P t Ab) T (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) u (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A B D pair H) (@homology_record_test_cover C P t Ab A B D pair H T u);

symbol homology_record_test_cover_lift [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (T : τ (Obj C)) (u : τ (Hom C T (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) : τ (Hom C (@homology_record_test_cover_object C P t Ab A B D pair
    H T u) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H))
≔ @computational_fiber_product_proj2 C P t (@abelian_stability_additive C P t Ab) T (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) u (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A B D pair H) (@homology_record_test_cover C P t Ab A B D pair H T u);

symbol homology_record_test_cover_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (T : τ (Obj C)) (u : τ (Hom C T (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H)))
  : τ (@IsEpic C (@homology_record_test_cover_object C P t Ab A B D pair H T u) T (@homology_record_test_cover_epi C P t Ab A B D
    pair H T u))
≔ @abelian_fiber_product_epic_projection C P t Ab T (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_cycle_object C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) u (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection_epic C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
      D pair H);

symbol homology_record_test_cover_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (T : τ (Obj C)) (u : τ (Hom C T (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H)))
  : τ (@= (Hom C (@homology_record_test_cover_object C P t Ab A B D pair H T u) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H))
      (@comp_fapp0 C (@homology_record_test_cover_object C P t Ab A B D pair H T u) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) (@homology_record_test_cover_lift C P t Ab A B D pair H T u))
      (@comp_fapp0 C (@homology_record_test_cover_object C P t Ab A B D pair H T u) T (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) u
        (@homology_record_test_cover_epi C P t Ab A B D pair H T u)))
≔ @eq_sym _ _ _ (@computational_fiber_product_compatibility_path C P t (@abelian_stability_additive C P t Ab) T
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) u (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A B D pair H) (@homology_record_test_cover C P t Ab A B D pair H T u));

symbol homology_map_kernel_boundary_zero
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
  : τ (@= (Hom C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))
      (@comp_fapp0 C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
        B1 D1 p1 H1) (@comp_fapp0 C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) z
        (@homology_record_test_cover_lift C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test))))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)))
≔ @eq_trans _ _ _ _
    (@hom_factor_paste_path C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) T (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1)
      (@homology_record_test_cover_epi C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_projection C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_test_cover_lift C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) z (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
        p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf)
      (@homology_record_test_cover_path C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test))
      (@eq_sym _ _ _ (@hom_precomp_factor_path C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf)))
    (@preadditive_precompose_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) T (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@comp_fapp0 C T (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
        t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
        p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_test_cover_epi C P t Ab A0 B0 D0 p0 H0 T
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
        Ab)) A1 B1 D1 p1 H1) z) hf) T test))
      (@weak_kernel_annihilator_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
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
        Ab)) A1 B1 D1 p1 H1) z) hf) T test));

symbol homology_map_kernel_boundary_test
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
  : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A1 B1 D1 p1 H1) (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T test)))
≔ @Struct_sigma (Hom C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
  (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A1 B1 D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))
    (λ h : τ (Hom C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)), @= (Hom C (@homology_record_test_cover_object C P t Ab A0 B0
      D0 p0 H0 T (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
      t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
      B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1))
      (@comp_fapp0 C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
        B1 D1 p1 H1) h) (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)))
    (@comp_fapp0 C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) z
      (@homology_record_test_cover_lift C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test))) (@homology_map_kernel_boundary_zero C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test);

symbol homology_map_kernel_cover
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
  : τ (@ComputationalExactCoverWitness C P t (@computational_abelian_preabelian C P t Ab) A1 (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@cokernel_record_row_pair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1 p1 H1) (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A1 B1 D1 p1 H1) (@homology_record_cokernel C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A1 B1 D1 p1 H1)) (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_boundary_test C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
≔ @abelian_cokernel_record_cover_explicit C P t (@computational_abelian_preabelian C P t Ab)
      (@computational_abelian_mono_lifts C P t Ab)
      (@computational_abelian_epi_colifts C P t Ab)
      A1 (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 p1 H1) (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
        P t Ab)) A1 B1 D1 p1 H1) (@homology_record_cokernel C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T
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
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_boundary_test C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
        test);

// Direct Sigma projections avoid reconstructing the erased row/test indices.
symbol homology_map_kernel_cover_object [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    B1 D1 p1 H1) z) hf) T)) : τ (Obj C)
≔ sigma_Fst (@homology_map_kernel_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test);

symbol homology_map_kernel_cover_step [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    B1 D1 p1 H1) z) hf) T)) : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T test)))
≔ sigma_Fst (sigma_Snd (@homology_map_kernel_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test));

symbol homology_map_kernel_cover_step_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  : τ (@IsEpic C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
    p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
    H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
≔ sigma_Fst (sigma_Snd (sigma_Snd (@homology_map_kernel_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)));

symbol homology_map_kernel_cover_boundary [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    B1 D1 p1 H1) z) hf) T)) : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1)
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd (@homology_map_kernel_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))));

symbol homology_map_kernel_cover_epi [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    B1 D1 p1 H1) z) hf) T)) : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T)
≔ @comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
  (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
  (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A1 B1 D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) T (@homology_record_test_cover_epi C P t Ab A0 B0 D0 p0 H0 T
  (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0
  H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A1 B1 D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test);

symbol homology_map_kernel_cover_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  : τ (@IsEpic C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T
    (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
≔ @is_epic_comp C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
  (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
  (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A1 B1 D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) T (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
  (@homology_record_test_cover_epi C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1
  H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
  D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  p1 H1) z) hf) T test))
    (@homology_map_kernel_cover_step_is_epic C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    (@homology_record_test_cover_is_epic C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test));

symbol homology_map_kernel_cover_cycles [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    B1 D1 p1 H1) z) hf) T)) : τ (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
    D0 p0 H0))
≔ @comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
  (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
  (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A1 B1 D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_test_cover_lift C P t Ab A0 B0 D0 p0 H0 T
  (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0
  H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  A1 B1 D1 p1 H1) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A1 B1 D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test);

symbol homology_map_kernel_cover_source_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0))
      (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1
        p0 p1 H0 H1 z hf T test))
      (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) T
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
        Ab)) A1 B1 D1 p1 H1) z) hf) T test) (@homology_map_kernel_cover_epi C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
      (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_projection C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_test_cover_lift C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)) (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0
        A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0))
        (λ h : τ (Hom C (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
          t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
          t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)), @comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab
          A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T
          (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
          D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
          Ab)) A1 B1 D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C
          P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
          t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
          t Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) h (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1
          D1 p0 p1 H0 H1 z hf T test))
        _ _ (@homology_record_test_cover_path C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
          t Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
          (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
          (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
          (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
          D1 p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
          t Ab)) A1 B1 D1 p1 H1) z) hf) T test)))
      (@eq_sym _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
        (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) T (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A1 B1 D1 p1 H1) z) hf) T test) (@homology_record_test_cover_epi C P t Ab A0 B0 D0 p0 H0 T
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
        Ab)) A1 B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T
        test))));

symbol homology_map_kernel_cover_target_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
  : τ (@= (Hom C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1
    D1 p1 H1))
      (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test) A1
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
        B1 D1 p1 H1) (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
        t Ab)) A1 B1 D1 p1 H1) (@homology_map_kernel_cover_boundary C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test))
      (@comp_fapp0 C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
        B0 D0 p0 H0) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) A1 B1 D1 p1 H1) z (@homology_map_kernel_cover_cycles C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)))
≔ @eq_trans _ _ _ _
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd (@homology_map_kernel_cover C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)))))
    (@eq_sym _ _ _ (@comp_assoc C (@homology_map_kernel_cover_object C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)
      (@homology_record_test_cover_object C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1) z
      (@homology_record_test_cover_lift C P t Ab A0 B0 D0 p0 H0 T (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@hom_precomp_factor_arrow C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0
      D0 p0 H0) (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 p0 H0) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 p1 H1)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      p1 H1) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A1 B1 D1 p1 H1) z) hf) T test)) (@homology_map_kernel_cover_step C P t Ab A0 B0 D0 A1 B1 D1 p0 p1 H0 H1 z hf T test)));
