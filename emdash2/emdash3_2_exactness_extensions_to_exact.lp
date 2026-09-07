/* Monomorphic local extensions imply the active computational exactness. */

require open emdash.emdash3_2_exactness_extensions_to_exact_zero;

symbol computational_exact_pushout_inj2_boundary_cokernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D))
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  (extensions : τ (@HasComputationalExactExtensions C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@= (Hom C
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H))
      (@comp_fapp0 C _ _ _
        (@computational_exact_boundary_pushout_inj2 C P t
          Ab A B D pair H)
        (@computational_exact_boundary_cokernel_projection C P t
          Ab A B D pair H))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_homology_cycle_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H)))
≔ @monic_postcomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_pushout_object C P t
      Ab A B D pair H)
    (@computational_exact_extension_object C P t
      (@abelian_stability_preabelian C P t Ab)
      A B D pair
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_cocone C P t
        Ab A B D pair H)
      (@computational_exact_boundary_extension C P t
        Ab A B D pair H extensions))
    (@computational_exact_extension_monomorphism C P t
      (@abelian_stability_preabelian C P t Ab)
      A B D pair
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_cocone C P t
        Ab A B D pair H)
      (@computational_exact_boundary_extension C P t
        Ab A B D pair H extensions))
    (@computational_exact_extension_is_monic C P t
      (@abelian_stability_preabelian C P t Ab)
      A B D pair
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_cocone C P t
        Ab A B D pair H)
      (@computational_exact_boundary_extension C P t
        Ab A B D pair H extensions))
    (@comp_fapp0 C _ _ _
      (@computational_exact_boundary_pushout_inj2 C P t
        Ab A B D pair H)
      (@computational_exact_boundary_cokernel_projection C P t
        Ab A B D pair H))
    (@computational_exact_extension_boundary_cokernel_zero_path C P t
      Ab A B D pair H extensions);

symbol computational_exact_boundary_cokernel_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D))
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  (extensions : τ (@HasComputationalExactExtensions C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@= (Hom C
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_exact_boundary_cokernel_object C P t
        Ab A B D pair H))
      (@computational_exact_boundary_cokernel_projection C P t
        Ab A B D pair H)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_homology_cycle_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_exact_boundary_cokernel_object C P t
          Ab A B D pair H)))
≔ @monic_postcomposition_zero_to_zero_path C
    (@abelian_stability_preadditive C P t Ab)
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_object C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout_object C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout_inj2 C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout_inj2_monic C P t
      Ab A B D pair H)
    (@computational_exact_boundary_cokernel_projection C P t
      Ab A B D pair H)
    (@computational_exact_pushout_inj2_boundary_cokernel_zero_path C P t
      Ab A B D pair H extensions);

symbol computational_exact_at_from_extensions
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D))
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  (extensions : τ (@HasComputationalExactExtensions C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@ComputationalExactAt C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
≔ @computational_cokernel_zero_to_epic C
    (@abelian_stability_preadditive C P t Ab)
    A
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel C P t Ab A B D pair H)
    (@computational_exact_boundary_cokernel_zero_path C P t
      Ab A B D pair H extensions);
