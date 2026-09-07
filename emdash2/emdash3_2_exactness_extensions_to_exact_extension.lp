/* Apply exact extensions to the boundary-cokernel pushout cocone. */

require open emdash.emdash3_2_exactness_extensions_to_exact_foundation;

symbol computational_exact_boundary_pushout_incoming_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D))
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@= (Hom C A
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H))
      (@comp_fapp0 C _ _ _
        (@computational_exact_boundary_pushout_inj1 C P t
          Ab A B D pair H)
        (@computational_chain_pair_dnext C
          (@abelian_stability_preadditive C P t Ab) A B D pair))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab) A
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H)))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C A B)
      (Hom C A
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H))
      (λ h : τ (Hom C A B),
        @comp_fapp0 C _ _ _
          (@computational_exact_boundary_pushout_inj1 C P t
            Ab A B D pair H) h)
      _ _
      (@eq_sym _ _ _
        (@computational_homology_boundary_path C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@computational_exact_boundary_pushout_inj1 C P t
          Ab A B D pair H)
        (@computational_homology_cycle_embedding C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_homology_boundary C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@computational_homology_cycle_object C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair H)
            (@computational_exact_boundary_pushout_object C P t
              Ab A B D pair H))
          (Hom C A
            (@computational_exact_boundary_pushout_object C P t
              Ab A B D pair H))
          (λ h : τ (Hom C
              (@computational_homology_cycle_object C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)
              (@computational_exact_boundary_pushout_object C P t
                Ab A B D pair H)),
            @comp_fapp0 C _ _ _ h
              (@computational_homology_boundary C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H))
          _ _
          (@computational_pushout_compatibility_path C P t
            (@abelian_stability_additive C P t Ab)
            B
            (@computational_homology_cycle_object C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair H)
            (@computational_exact_boundary_cokernel_object C P t
              Ab A B D pair H)
            (@computational_homology_cycle_embedding C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair H)
            (@computational_exact_boundary_cokernel_projection C P t
              Ab A B D pair H)
            (@computational_exact_boundary_pushout C P t
              Ab A B D pair H)))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@computational_exact_boundary_pushout_inj2 C P t
                Ab A B D pair H)
              (@computational_exact_boundary_cokernel_projection C P t
                Ab A B D pair H)
              (@computational_homology_boundary C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)))
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C A
                (@computational_exact_boundary_cokernel_object C P t
                  Ab A B D pair H))
              (Hom C A
                (@computational_exact_boundary_pushout_object C P t
                  Ab A B D pair H))
              (λ h : τ (Hom C A
                  (@computational_exact_boundary_cokernel_object C P t
                    Ab A B D pair H)),
                @comp_fapp0 C _ _ _
                  (@computational_exact_boundary_pushout_inj2 C P t
                    Ab A B D pair H) h)
              _ _
              (@computational_cokernel_annihilation C
                (@abelian_stability_preadditive C P t Ab)
                A
                (@computational_homology_cycle_object C P t
                  (@abelian_stability_preabelian C P t Ab) A B D pair H)
                (@computational_homology_boundary C P t
                  (@abelian_stability_preabelian C P t Ab) A B D pair H)
                (@computational_exact_boundary_cokernel C P t
                  Ab A B D pair H)))
            (@preadditive_comp_zero_right_path C
              (@abelian_stability_preadditive C P t Ab)
              A
              (@computational_exact_boundary_cokernel_object C P t
                Ab A B D pair H)
              (@computational_exact_boundary_pushout_object C P t
                Ab A B D pair H)
              (@computational_exact_boundary_pushout_inj2 C P t
                Ab A B D pair H))))));

symbol computational_exact_boundary_pushout_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D))
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@CokernelCoannihilator C
      (@abelian_stability_preadditive C P t Ab)
      A B
      (@computational_chain_pair_dnext C
        (@abelian_stability_preadditive C P t Ab) A B D pair)
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H))
≔ @Struct_sigma
    (Hom C B
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H))
    (λ h : τ (Hom C B
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H)),
      @= (Hom C A
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H))
        (@comp_fapp0 C _ _ _ h
          (@computational_chain_pair_dnext C
            (@abelian_stability_preadditive C P t Ab) A B D pair))
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) A
          (@computational_exact_boundary_pushout_object C P t
            Ab A B D pair H)))
    (@computational_exact_boundary_pushout_inj1 C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout_incoming_zero_path C P t
      Ab A B D pair H);

symbol computational_exact_boundary_extension
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
  : τ (@ComputationalExactExtensionWitness C P t
      (@abelian_stability_preabelian C P t Ab)
      A B D pair
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_cocone C P t
        Ab A B D pair H))
≔ extensions
    (@computational_exact_boundary_pushout_object C P t Ab A B D pair H)
    (@computational_exact_boundary_pushout_cocone C P t Ab A B D pair H);
