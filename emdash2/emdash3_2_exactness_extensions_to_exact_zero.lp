/* The selected extension kills the boundary-cokernel projection after q2. */

require open emdash.emdash3_2_exactness_extensions_to_exact_extension;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol computational_exact_extension_boundary_cokernel_zero_path
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
      (@computational_exact_extension_object C P t
        (@abelian_stability_preabelian C P t Ab)
        A B D pair
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H)
        (@computational_exact_boundary_pushout_cocone C P t
          Ab A B D pair H)
        (@computational_exact_boundary_extension C P t
          Ab A B D pair H extensions)))
      (@comp_fapp0 C _ _ _
        (@computational_exact_extension_monomorphism C P t
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
            Ab A B D pair H)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@computational_homology_cycle_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_exact_extension_object C P t
          (@abelian_stability_preabelian C P t Ab)
          A B D pair
          (@computational_exact_boundary_pushout_object C P t
            Ab A B D pair H)
          (@computational_exact_boundary_pushout_cocone C P t
            Ab A B D pair H)
          (@computational_exact_boundary_extension C P t
            Ab A B D pair H extensions))))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C
        (@computational_homology_cycle_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_exact_boundary_pushout_object C P t
          Ab A B D pair H))
      (Hom C
        (@computational_homology_cycle_object C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)
        (@computational_exact_extension_object C P t
          (@abelian_stability_preabelian C P t Ab)
          A B D pair
          (@computational_exact_boundary_pushout_object C P t
            Ab A B D pair H)
          (@computational_exact_boundary_pushout_cocone C P t
            Ab A B D pair H)
          (@computational_exact_boundary_extension C P t
            Ab A B D pair H extensions)))
      (λ h : τ (Hom C
          (@computational_homology_cycle_object C P t
            (@abelian_stability_preabelian C P t Ab) A B D pair H)
          (@computational_exact_boundary_pushout_object C P t
            Ab A B D pair H)),
        @comp_fapp0 C _ _ _
          (@computational_exact_extension_monomorphism C P t
            (@abelian_stability_preabelian C P t Ab)
            A B D pair
            (@computational_exact_boundary_pushout_object C P t
              Ab A B D pair H)
            (@computational_exact_boundary_pushout_cocone C P t
              Ab A B D pair H)
            (@computational_exact_boundary_extension C P t
              Ab A B D pair H extensions)) h)
      _ _
      (@eq_sym _ _ _
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
            Ab A B D pair H))))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@computational_exact_extension_monomorphism C P t
          (@abelian_stability_preabelian C P t Ab)
          A B D pair
          (@computational_exact_boundary_pushout_object C P t
            Ab A B D pair H)
          (@computational_exact_boundary_pushout_cocone C P t
            Ab A B D pair H)
          (@computational_exact_boundary_extension C P t
            Ab A B D pair H extensions))
        (@computational_exact_boundary_pushout_inj1 C P t
          Ab A B D pair H)
        (@computational_homology_cycle_embedding C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C B
            (@computational_exact_extension_object C P t
              (@abelian_stability_preabelian C P t Ab)
              A B D pair
              (@computational_exact_boundary_pushout_object C P t
                Ab A B D pair H)
              (@computational_exact_boundary_pushout_cocone C P t
                Ab A B D pair H)
              (@computational_exact_boundary_extension C P t
                Ab A B D pair H extensions)))
          (Hom C
            (@computational_homology_cycle_object C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair H)
            (@computational_exact_extension_object C P t
              (@abelian_stability_preabelian C P t Ab)
              A B D pair
              (@computational_exact_boundary_pushout_object C P t
                Ab A B D pair H)
              (@computational_exact_boundary_pushout_cocone C P t
                Ab A B D pair H)
              (@computational_exact_boundary_extension C P t
                Ab A B D pair H extensions)))
          (λ h : τ (Hom C B
              (@computational_exact_extension_object C P t
                (@abelian_stability_preabelian C P t Ab)
                A B D pair
                (@computational_exact_boundary_pushout_object C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_pushout_cocone C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_extension C P t
                  Ab A B D pair H extensions))),
            @comp_fapp0 C _ _ _ h
              (@computational_homology_cycle_embedding C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H))
          _ _
          (@computational_exact_extension_path C P t
            (@abelian_stability_preabelian C P t Ab)
            A B D pair
            (@computational_exact_boundary_pushout_object C P t
              Ab A B D pair H)
            (@computational_exact_boundary_pushout_cocone C P t
              Ab A B D pair H)
            (@computational_exact_boundary_extension C P t
              Ab A B D pair H extensions)))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@computational_exact_extension_factor C P t
                (@abelian_stability_preabelian C P t Ab)
                A B D pair
                (@computational_exact_boundary_pushout_object C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_pushout_cocone C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_extension C P t
                  Ab A B D pair H extensions))
              (@computational_chain_pair_d C
                (@abelian_stability_preadditive C P t Ab) A B D pair)
              (@computational_homology_cycle_embedding C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)))
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C
                (@computational_homology_cycle_object C P t
                  (@abelian_stability_preabelian C P t Ab) A B D pair H)
                D)
              (Hom C
                (@computational_homology_cycle_object C P t
                  (@abelian_stability_preabelian C P t Ab) A B D pair H)
                (@computational_exact_extension_object C P t
                  (@abelian_stability_preabelian C P t Ab)
                  A B D pair
                  (@computational_exact_boundary_pushout_object C P t
                    Ab A B D pair H)
                  (@computational_exact_boundary_pushout_cocone C P t
                    Ab A B D pair H)
                  (@computational_exact_boundary_extension C P t
                    Ab A B D pair H extensions)))
              (λ h : τ (Hom C
                  (@computational_homology_cycle_object C P t
                    (@abelian_stability_preabelian C P t Ab) A B D pair H)
                  D),
                @comp_fapp0 C _ _ _
                  (@computational_exact_extension_factor C P t
                    (@abelian_stability_preabelian C P t Ab)
                    A B D pair
                    (@computational_exact_boundary_pushout_object C P t
                      Ab A B D pair H)
                    (@computational_exact_boundary_pushout_cocone C P t
                      Ab A B D pair H)
                    (@computational_exact_boundary_extension C P t
                      Ab A B D pair H extensions)) h)
              _ _
              (@computational_kernel_annihilation C
                (@abelian_stability_preadditive C P t Ab)
                B D
                (@computational_chain_pair_d C
                  (@abelian_stability_preadditive C P t Ab) A B D pair)
                (@computational_homology_cycles C P t
                  (@abelian_stability_preabelian C P t Ab) A B D pair H)))
            (@preadditive_comp_zero_right_path C
              (@abelian_stability_preadditive C P t Ab)
              (@computational_homology_cycle_object C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)
              D
              (@computational_exact_extension_object C P t
                (@abelian_stability_preabelian C P t Ab)
                A B D pair
                (@computational_exact_boundary_pushout_object C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_pushout_cocone C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_extension C P t
                  Ab A B D pair H extensions))
              (@computational_exact_extension_factor C P t
                (@abelian_stability_preabelian C P t Ab)
                A B D pair
                (@computational_exact_boundary_pushout_object C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_pushout_cocone C P t
                  Ab A B D pair H)
                (@computational_exact_boundary_extension C P t
                  Ab A B D pair H extensions)))))));
