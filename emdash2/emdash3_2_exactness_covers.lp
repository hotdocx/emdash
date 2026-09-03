/* Epimorphic local covers imply the active computational exactness notion. */

require open emdash.emdash3_2_exactness_covers_foundation;

symbol computational_exact_cycle_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  : τ (@WeakKernelAnnihilator C
      (@computational_homology_preadditive C P t Abl)
      B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair)
      (@computational_homology_cycle_object C P t Abl A B D pair H))
≔ @Struct_sigma
    (Hom C
      (@computational_homology_cycle_object C P t Abl A B D pair H) B)
    (λ h : τ (Hom C
        (@computational_homology_cycle_object C P t Abl A B D pair H) B),
      @= (Hom C
        (@computational_homology_cycle_object C P t Abl A B D pair H) D)
        (@comp_fapp0 C _ _ _
          (@computational_chain_pair_d C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          h)
        (@preadditive_hom_zero C
          (@computational_homology_preadditive C P t Abl)
          (@computational_homology_cycle_object C P t Abl A B D pair H) D))
    (@computational_homology_cycle_embedding C P t Abl A B D pair H)
    (@computational_kernel_annihilation C
      (@computational_homology_preadditive C P t Abl)
      B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair)
      (@computational_homology_cycles C P t Abl A B D pair H));

symbol computational_exact_cycle_cover
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  (covers : τ (@HasComputationalExactCovers C P t Abl A B D pair))
  : τ (@ComputationalExactCoverWitness C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H))
≔ covers
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_exact_cycle_cone C P t Abl A B D pair H);

symbol computational_exact_boundary_after_cover_factor_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Abl : τ (@PreAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D)]
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  (covers : τ (@HasComputationalExactCovers C P t Abl A B D pair))
  : τ (@= (Hom C
      (@computational_exact_cover_object C P t Abl A B D pair
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@computational_exact_cycle_cone C P t Abl A B D pair H)
        (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
      (@computational_homology_cycle_object C P t Abl A B D pair H))
      (@comp_fapp0 C _ _ _
        (@computational_homology_boundary C P t Abl A B D pair H)
        (@computational_exact_cover_factor C P t Abl A B D pair
          (@computational_homology_cycle_object C P t Abl A B D pair H)
          (@computational_exact_cycle_cone C P t Abl A B D pair H)
          (@computational_exact_cycle_cover C P t Abl A B D pair H covers)))
      (@computational_exact_cover_epimorphism C P t Abl A B D pair
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@computational_exact_cycle_cone C P t Abl A B D pair H)
        (@computational_exact_cycle_cover C P t Abl A B D pair H covers)))
≔ (@computational_kernel_morphism_is_monic C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    (@computational_homology_cycles C P t Abl A B D pair H))
    (@computational_exact_cover_object C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H)
      (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
    (@comp_fapp0 C _ _ _
      (@computational_homology_boundary C P t Abl A B D pair H)
      (@computational_exact_cover_factor C P t Abl A B D pair
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@computational_exact_cycle_cone C P t Abl A B D pair H)
        (@computational_exact_cycle_cover C P t Abl A B D pair H covers)))
    (@computational_exact_cover_epimorphism C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H)
      (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@computational_homology_cycle_embedding C P t Abl A B D pair H)
        (@computational_homology_boundary C P t Abl A B D pair H)
        (@computational_exact_cover_factor C P t Abl A B D pair
          (@computational_homology_cycle_object C P t Abl A B D pair H)
          (@computational_exact_cycle_cone C P t Abl A B D pair H)
          (@computational_exact_cycle_cover C P t Abl A B D pair H covers)))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C A B)
          (Hom C
            (@computational_exact_cover_object C P t Abl A B D pair
              (@computational_homology_cycle_object C P t Abl A B D pair H)
              (@computational_exact_cycle_cone C P t Abl A B D pair H)
              (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
            B)
          (λ h : τ (Hom C A B),
            @comp_fapp0 C _ _ _ h
              (@computational_exact_cover_factor C P t Abl A B D pair
                (@computational_homology_cycle_object C P t Abl A B D pair H)
                (@computational_exact_cycle_cone C P t Abl A B D pair H)
                (@computational_exact_cycle_cover C P t Abl
                  A B D pair H covers)))
          _ _
          (@computational_homology_boundary_path C P t Abl A B D pair H))
        (@computational_exact_cover_path C P t Abl A B D pair
          (@computational_homology_cycle_object C P t Abl A B D pair H)
          (@computational_exact_cycle_cone C P t Abl A B D pair H)
          (@computational_exact_cycle_cover C P t Abl A B D pair H covers))));

symbol computational_exact_at_from_covers
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  (covers : τ (@HasComputationalExactCovers C P t Abl A B D pair))
  : τ (@ComputationalExactAt C P t Abl A B D pair H)
≔ @is_epic_of_epic_factor C
    (@computational_exact_cover_object C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H)
      (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
    A
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_exact_cover_factor C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H)
      (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
    (@computational_homology_boundary C P t Abl A B D pair H)
    (@computational_exact_cover_epimorphism C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H)
      (@computational_exact_cycle_cover C P t Abl A B D pair H covers))
    (@computational_exact_boundary_after_cover_factor_path C P t
      Abl A B D pair H covers)
    (@computational_exact_cover_is_epic C P t Abl A B D pair
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_exact_cycle_cone C P t Abl A B D pair H)
      (@computational_exact_cycle_cover C P t Abl A B D pair H covers));

// Any epic point of the selected kernel-factor fibre proves exactness; fibre
// contractibility transports epicity back to the actual selected boundary.
symbol computational_exact_at_from_epic_factor_point
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Abl : τ (@PreAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@computational_homology_preadditive C P t Abl) A B D))
  (H : τ (@ComputationalHomologyAt C P t Abl A B D pair))
  (point : τ (@KernelFactorSpace C
    (@computational_homology_preadditive C P t Abl)
    B D
    (@computational_chain_pair_d C
      (@computational_homology_preadditive C P t Abl) A B D pair)
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@computational_homology_cycle_embedding C P t Abl A B D pair H)
    A
    (@computational_chain_pair_cone C
      (@computational_homology_preadditive C P t Abl) A B D pair)))
  (epic : τ (@IsEpic C A
    (@computational_homology_cycle_object C P t Abl A B D pair H)
    (@hfiber_point
      (Hom C A
        (@computational_homology_cycle_object C P t Abl A B D pair H))
      (Hom C A B)
      (λ h : τ (Hom C A
          (@computational_homology_cycle_object C P t Abl A B D pair H)),
        @comp_fapp0 C _ _ _
          (@computational_homology_cycle_embedding C P t Abl A B D pair H) h)
      (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t Abl) A B D pair)
      point)))
  : τ (@ComputationalExactAt C P t Abl A B D pair H)
≔ @ind_eq
    (@KernelFactorSpace C
      (@computational_homology_preadditive C P t Abl)
      B D
      (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t Abl) A B D pair)
      (@computational_homology_cycle_object C P t Abl A B D pair H)
      (@computational_homology_cycle_embedding C P t Abl A B D pair H)
      A
      (@computational_chain_pair_cone C
        (@computational_homology_preadditive C P t Abl) A B D pair))
    (is_contr_center
      (@computational_kernel_factor_contr C
        (@computational_homology_preadditive C P t Abl)
        B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        (@computational_homology_cycles C P t Abl A B D pair H)
        A
        (@computational_chain_pair_cone C
          (@computational_homology_preadditive C P t Abl) A B D pair)))
    point
    (is_contr_path
      (@computational_kernel_factor_contr C
        (@computational_homology_preadditive C P t Abl)
        B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        (@computational_homology_cycles C P t Abl A B D pair H)
        A
        (@computational_chain_pair_cone C
          (@computational_homology_preadditive C P t Abl) A B D pair))
      point)
    (λ factor : τ (@KernelFactorSpace C
        (@computational_homology_preadditive C P t Abl)
        B D
        (@computational_chain_pair_d C
          (@computational_homology_preadditive C P t Abl) A B D pair)
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@computational_homology_cycle_embedding C P t Abl A B D pair H)
        A
        (@computational_chain_pair_cone C
          (@computational_homology_preadditive C P t Abl) A B D pair)),
      @IsEpic C A
        (@computational_homology_cycle_object C P t Abl A B D pair H)
        (@hfiber_point
          (Hom C A
            (@computational_homology_cycle_object C P t Abl A B D pair H))
          (Hom C A B)
          (λ h : τ (Hom C A
              (@computational_homology_cycle_object C P t Abl A B D pair H)),
            @comp_fapp0 C _ _ _
              (@computational_homology_cycle_embedding C P t
                Abl A B D pair H) h)
          (@computational_chain_pair_dnext C
            (@computational_homology_preadditive C P t Abl) A B D pair)
          factor))
    epic;
