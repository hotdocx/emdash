/* Both cover reconstructions and epicity retain their actual supplied maps. */
require open emdash.emdash3_2_homology_epic_covers;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    pair H) z) hf) T)) ⊢
  @homology_epic_boundary_source_path C P t Ab A B D X Y pair H e z hf T test
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
        Ab)) A B D pair H) z) hf) T test) (@homology_epic_boundary_projection C P t Ab A B D X Y pair H e z hf T test)));

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    pair H) z) hf) T)) ⊢
  @homology_epic_boundary_target_path C P t Ab A B D X Y pair H e z hf T test
  : τ (@= (Hom C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H))
      (@comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) A (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H)
        (@homology_record_boundary C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D
        pair H) (@homology_epic_boundary_preimage C P t Ab A B D X Y pair H e z hf T test))
      (@comp_fapp0 C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) Y (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair H) z
        (@homology_epic_boundary_lift C P t Ab A B D X Y pair H e z hf T test)));

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    pair H) z) hf) T)) (epic : τ (@IsEpic C Y X e)) ⊢
  @homology_epic_boundary_is_epic C P t Ab A B D X Y pair H e z hf T test epic
  : τ (@IsEpic C (@homology_epic_boundary_object C P t Ab A B D X Y pair H e z hf T test) T (@homology_epic_boundary_projection C P
    t Ab A B D X Y pair H e z hf T test));
