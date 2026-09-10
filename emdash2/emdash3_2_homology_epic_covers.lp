/*
  Epic presentations and retained target-boundary covers.
  Pull back an annihilated test along its supplied epic presentation, then
  cover the resulting target-boundary test. The existing pullback and
  exact-cover records own every operation; no section or new cone type is used.
*/
require open emdash.emdash3_2_cokernel_record_covers;
require open emdash.emdash3_2_hom_factor_composition;

symbol homology_epic_test_pullback [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (@ComputationalFiberProduct C P t (@abelian_stability_additive C P t Ab) T X Y
    (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
    (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair
    H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T test) e)
≔ @abelian_selected_fiber_product C P t Ab T X Y (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A
  B D pair H) z) hf) T test) e;

symbol homology_epic_test_object [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Obj C)
≔ @computational_fiber_product_object C P t (@abelian_stability_additive C P t Ab) T X Y (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@hom_precomp_factor_arrow
  C Y X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_projection C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z) hf) T test) e (@homology_epic_test_pullback C P t Ab A B D X Y
  pair H e z hf T test);

symbol homology_epic_test_projection [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) T)
≔ @computational_fiber_product_proj1 C P t (@abelian_stability_additive C P t Ab) T X Y (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@hom_precomp_factor_arrow
  C Y X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_projection C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z) hf) T test) e (@homology_epic_test_pullback C P t Ab A B D X Y
  pair H e z hf T test);

symbol homology_epic_test_lift [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) Y)
≔ @computational_fiber_product_proj2 C P t (@abelian_stability_additive C P t Ab) T X Y (@weak_kernel_annihilator_arrow C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@hom_precomp_factor_arrow
  C Y X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_projection C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z) hf) T test) e (@homology_epic_test_pullback C P t Ab A B D X Y
  pair H e z hf T test);

symbol homology_epic_test_projection_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) (epic : τ (@IsEpic C Y X e))
  : τ (@IsEpic C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) T (@homology_epic_test_projection C P t Ab A B
    D X Y pair H e z hf T test))
≔ @abelian_fiber_product_epic_projection C P t Ab T X Y (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
  pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A
  B D pair H) z) hf) T test) e epic;

symbol homology_epic_test_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@= (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) X) (@comp_fapp0 C (@homology_epic_test_object
    C P t Ab A B D X Y pair H e z hf T test) Y X e (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test))
      (@comp_fapp0 C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) T X (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) z) hf) T test) (@homology_epic_test_projection C P t Ab A B D X Y pair H e z hf T test)))
≔ @eq_sym _ _ _ (@computational_fiber_product_compatibility_path C P t (@abelian_stability_additive C P t Ab) T X Y
  (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
  (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
  (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
  (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair
  H) z) hf) T test) e (@homology_epic_test_pullback C P t Ab A B D X Y pair H e z hf T test));

symbol homology_epic_boundary_zero [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@= (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)) (@comp_fapp0 C
    (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@comp_fapp0 C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z
    (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test)))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)))
≔ @eq_trans _ _ _ _
    (@hom_factor_paste_path C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) T Y X
      (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
      D pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A B D pair H) (@homology_epic_test_projection C P t Ab A B D X Y pair H e z hf T test) e (@homology_record_projection C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
      (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test) z (@weak_kernel_annihilator_arrow C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
      (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair
      H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
      D pair H) z) hf) T test) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P
      t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
      (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair
      H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
      D pair H) z) hf)
      (@homology_epic_test_path C P t Ab A B D X Y pair H e z hf T test)
      (@eq_sym _ _ _ (@hom_precomp_factor_path C Y X (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) z) hf)))
    (@preadditive_precompose_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) T (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
      (@comp_fapp0 C T X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
        P t Ab)) A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P
        t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) z) hf) (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
        (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A
        B D pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) z) hf) T test)) (@homology_epic_test_projection C P t Ab A B D X
        Y pair H e z hf T test)
      (@weak_kernel_annihilator_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) z) hf) T test));

symbol homology_epic_boundary_test [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test))
≔ @Struct_sigma (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H))
    (λ a : τ (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)), @= (Hom C
      (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H))
      (@comp_fapp0 C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) a) (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)))
    (@comp_fapp0 C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) Y (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z
      (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test)) (@homology_epic_boundary_zero C P t Ab A B D X Y pair H e
      z hf T test);

symbol homology_epic_boundary_cover [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@ComputationalExactCoverWitness C P t (@computational_abelian_preabelian C P t Ab) A (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@cokernel_record_row_pair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A
    B D pair H) (@homology_record_cokernel C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H)) (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_boundary_test C P t Ab
    A B D X Y pair H e z hf T test))
≔ @abelian_cokernel_record_cover_explicit C P t (@computational_abelian_preabelian C P t Ab)
    (@computational_abelian_mono_lifts C P t Ab) (@computational_abelian_epi_colifts C P t Ab)
    A (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
      D pair H) (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
      Ab)) A B D pair H) (@homology_record_cokernel C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) A B D pair H) (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_boundary_test C
      P t Ab A B D X Y pair H e z hf T test);

symbol homology_epic_boundary_object [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Obj C)
≔ sigma_Fst (@homology_epic_boundary_cover C P t Ab A B D X Y pair H e z hf T test);

symbol homology_epic_boundary_step [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test)
    (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test))
≔ sigma_Fst (sigma_Snd (@homology_epic_boundary_cover C P t Ab A B D X Y pair H e z hf T test));

symbol homology_epic_boundary_step_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@IsEpic C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_test_object C P t Ab A B D
    X Y pair H e z hf T test) (@homology_epic_boundary_step C P t Ab A B D X Y pair H e z hf T test))
≔ sigma_Fst (sigma_Snd (sigma_Snd (@homology_epic_boundary_cover C P t Ab A B D X Y pair H e z hf T test)));

symbol homology_epic_boundary_preimage [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) A)
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd (@homology_epic_boundary_cover C P t Ab A B D X Y pair H e z hf T test))));

symbol homology_epic_boundary_lift [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) Y)
≔ @comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_test_object C P t Ab A B D
  X Y pair H e z hf T test) Y (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_boundary_step C P t
  Ab A B D X Y pair H e z hf T test);

symbol homology_epic_boundary_projection [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) : τ (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) T)
≔ @comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_test_object C P t Ab A B D
  X Y pair H e z hf T test) T (@homology_epic_test_projection C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_boundary_step
  C P t Ab A B D X Y pair H e z hf T test);

symbol homology_epic_boundary_is_epic [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T)) (epic : τ (@IsEpic C Y X e))
  : τ (@IsEpic C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) T (@homology_epic_boundary_projection C P
    t Ab A B D X Y pair H e z hf T test))
≔ @is_epic_comp C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_test_object C P t Ab A B
  D X Y pair H e z hf T test) T (@homology_epic_boundary_step C P t Ab A B D X Y pair H e z hf T test)
  (@homology_epic_test_projection C P t Ab A B D X Y pair H e z hf T test)
    (@homology_epic_boundary_step_is_epic C P t Ab A B D X Y pair H e z hf T test)
    (@homology_epic_test_projection_is_epic C P t Ab A B D X Y pair H e z hf T test epic);

symbol homology_epic_boundary_source_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@= (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) X)
      (@comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) Y X e (@homology_epic_boundary_lift C
        P t Ab A B D X Y pair H e z hf T test))
      (@comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) T X (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) z) hf) T test) (@homology_epic_boundary_projection C P t Ab A B D X Y pair H e z hf T test)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_test_object C P t Ab A B
      D X Y pair H e z hf T test) Y X e (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test)
      (@homology_epic_boundary_step C P t Ab A B D X Y pair H e z hf T test))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) X) (Hom C (@homology_epic_boundary_object
        C P t Ab A B D X Y pair H e z hf T test) X)
        (λ h : τ (Hom C (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) X), @comp_fapp0 C
          (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_test_object C P t Ab A B D X Y
          pair H e z hf T test) X h (@homology_epic_boundary_step C P t Ab A B D X Y pair H e z hf T test)) _ _
        (@homology_epic_test_path C P t Ab A B D X Y pair H e z hf T test))
      (@eq_sym _ _ _ (@comp_assoc C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test)
        (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) T X (@weak_kernel_annihilator_arrow C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X (@homology_record_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A B D pair H) z) hf) T test) (@homology_epic_test_projection C P t Ab A B D X Y pair H e z hf T test)
        (@homology_epic_boundary_step C P t Ab A B D X Y pair H e z hf T test))));

symbol homology_epic_boundary_target_path [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D X Y : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
  (e : τ (Hom C Y X)) (z : τ (Hom C Y (@homology_record_cycle_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H))) (hf : τ (@HomPrecompFactor C Y X (@homology_record_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y
    (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B
    D pair H) (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) A B D pair H) z)))
  (T : τ (Obj C)) (test : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
    C P t Ab)) X (@homology_record_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    A B D pair H) (@hom_precomp_factor_arrow C Y X (@homology_record_object C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair H) e (@comp_fapp0 C Y (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) (@homology_record_object
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
    (@homology_record_projection C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
    pair H) z) hf) T))
  : τ (@= (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H))
      (@comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) A (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_epic_boundary_preimage C P t Ab A B D X Y pair H e z hf T test))
      (@comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z
        (@homology_epic_boundary_lift C P t Ab A B D X Y pair H e z hf T test)))
≔ @eq_trans _ _ _ _
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd (@homology_epic_boundary_cover C P t Ab A B D X Y pair H e z hf T test)))))
    (@eq_sym _ _ _ (@comp_assoc C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test)
      (@homology_epic_test_object C P t Ab A B D X Y pair H e z hf T test) Y (@homology_record_cycle_object C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z
      (@homology_epic_test_lift C P t Ab A B D X Y pair H e z hf T test) (@homology_epic_boundary_step C P t Ab A B D X Y pair H e z
      hf T test)));
