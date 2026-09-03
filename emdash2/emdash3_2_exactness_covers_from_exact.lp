/* Exactness supplies epimorphic local covers by a selected fiber product. */

require open emdash.emdash3_2_exactness_covers;
require open emdash.emdash3_2_abelian_fiber_pushout_stability;

symbol computational_exact_cone_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (Hom C T
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    (@computational_homology_cycles C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    T cone;

symbol computational_exact_cover_pullback
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (@ComputationalFiberProduct C P t
      (@abelian_stability_additive C P t Ab)
      T
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      A
      (@computational_exact_cone_lift C P t Ab A B D pair H T cone)
      (@computational_homology_boundary C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H))
≔ @abelian_selected_fiber_product C P t Ab
    T
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    A
    (@computational_exact_cone_lift C P t Ab A B D pair H T cone)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H);

symbol computational_exact_cover_pullback_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  [H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair)]
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (Obj C)
≔ @computational_fiber_product_object C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    A
    (@computational_exact_cone_lift C P t Ab A B D pair H T cone)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_cover_pullback C P t Ab A B D pair H T cone);

symbol computational_exact_cover_pullback_epi
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  [H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair)]
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (Hom C
      (@computational_exact_cover_pullback_object C P t
        Ab A B D pair H T cone)
      T)
≔ @computational_fiber_product_proj1 C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    A
    (@computational_exact_cone_lift C P t Ab A B D pair H T cone)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_cover_pullback C P t Ab A B D pair H T cone);

symbol computational_exact_cover_pullback_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  [H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair)]
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (Hom C
      (@computational_exact_cover_pullback_object C P t
        Ab A B D pair H T cone)
      A)
≔ @computational_fiber_product_proj2 C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    A
    (@computational_exact_cone_lift C P t Ab A B D pair H T cone)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_cover_pullback C P t Ab A B D pair H T cone);

symbol computational_exact_cover_pullback_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  [H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair)]
  (exact : τ (@ComputationalExactAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair H))
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (@IsEpic C
      (@computational_exact_cover_pullback_object C P t
        Ab A B D pair H T cone)
      T
      (@computational_exact_cover_pullback_epi C P t
        Ab A B D pair H T cone))
≔ @abelian_fiber_product_epic_projection C P t Ab
    T
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    A
    (@computational_exact_cone_lift C P t Ab A B D pair H T cone)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    exact;

symbol computational_exact_cover_pullback_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  [H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair)]
  [T : τ (Obj C)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    B D
    (@computational_chain_pair_d C
      (@abelian_stability_preadditive C P t Ab) A B D pair)
    T))
  : τ (@= (Hom C
      (@computational_exact_cover_pullback_object C P t
        Ab A B D pair H T cone)
      B)
      (@comp_fapp0 C _ _ _
        (@computational_chain_pair_dnext C
          (@abelian_stability_preadditive C P t Ab) A B D pair)
        (@computational_exact_cover_pullback_factor C P t
          Ab A B D pair H T cone))
      (@comp_fapp0 C _ _ _
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          B D
          (@computational_chain_pair_d C
            (@abelian_stability_preadditive C P t Ab) A B D pair)
          T cone)
        (@computational_exact_cover_pullback_epi C P t
          Ab A B D pair H T cone)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _
      (@eq_ap
        (Hom C A B)
        (Hom C
          (@computational_exact_cover_pullback_object C P t
            Ab A B D pair H T cone)
          B)
        (λ h : τ (Hom C A B),
          @comp_fapp0 C _ _ _ h
            (@computational_exact_cover_pullback_factor C P t
              Ab A B D pair H T cone))
        _ _
        (@computational_homology_boundary_path C P t
          (@abelian_stability_preabelian C P t Ab) A B D pair H)))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C _ _ _ _
          (@computational_homology_cycle_embedding C P t
            (@abelian_stability_preabelian C P t Ab) A B D pair H)
          (@computational_homology_boundary C P t
            (@abelian_stability_preabelian C P t Ab) A B D pair H)
          (@computational_exact_cover_pullback_factor C P t
            Ab A B D pair H T cone)))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@computational_exact_cover_pullback_object C P t
              Ab A B D pair H T cone)
            (@computational_homology_cycle_object C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair H))
          (Hom C
            (@computational_exact_cover_pullback_object C P t
              Ab A B D pair H T cone)
            B)
          (λ h : τ (Hom C
              (@computational_exact_cover_pullback_object C P t
                Ab A B D pair H T cone)
              (@computational_homology_cycle_object C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)),
            @comp_fapp0 C _ _ _
              (@computational_homology_cycle_embedding C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H) h)
          _ _
          (@eq_sym _ _ _
            (@computational_fiber_product_compatibility_path C P t
              (@abelian_stability_additive C P t Ab)
              T
              (@computational_homology_cycle_object C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)
              A
              (@computational_exact_cone_lift C P t
                Ab A B D pair H T cone)
              (@computational_homology_boundary C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)
              (@computational_exact_cover_pullback C P t
                Ab A B D pair H T cone))))
        (@eq_trans _ _ _ _
          (@comp_assoc C _ _ _ _
            (@computational_homology_cycle_embedding C P t
              (@abelian_stability_preabelian C P t Ab) A B D pair H)
            (@computational_exact_cone_lift C P t
              Ab A B D pair H T cone)
            (@computational_exact_cover_pullback_epi C P t
              Ab A B D pair H T cone))
          (@eq_ap
            (Hom C T B)
            (Hom C
              (@computational_exact_cover_pullback_object C P t
                Ab A B D pair H T cone)
              B)
            (λ h : τ (Hom C T B),
              @comp_fapp0 C _ _ _ h
                (@computational_exact_cover_pullback_epi C P t
                  Ab A B D pair H T cone))
            _ _
            (@computational_kernel_lift_path C
              (@abelian_stability_preadditive C P t Ab)
              B D
              (@computational_chain_pair_d C
                (@abelian_stability_preadditive C P t Ab) A B D pair)
              (@computational_homology_cycles C P t
                (@abelian_stability_preabelian C P t Ab) A B D pair H)
              T cone)))));

symbol computational_exact_covers_from_exact
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D))
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  (exact : τ (@ComputationalExactAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair H))
  : τ (@HasComputationalExactCovers C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair)
≔ λ T : τ (Obj C),
   λ cone : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      B D
      (@computational_chain_pair_d C
        (@abelian_stability_preadditive C P t Ab) A B D pair)
      T),
     @Struct_sigma
       (Obj C)
       (λ U : τ (Obj C),
         `Σ_ e : τ (Hom C U T),
         `Σ_ epic : τ (@IsEpic C U T e),
         `Σ_ a : τ (Hom C U A),
           @= (Hom C U B)
             (@comp_fapp0 C _ _ _
               (@computational_chain_pair_dnext C
                 (@abelian_stability_preadditive C P t Ab) A B D pair) a)
             (@comp_fapp0 C _ _ _
               (@weak_kernel_annihilator_arrow C
                 (@abelian_stability_preadditive C P t Ab)
                 B D
                 (@computational_chain_pair_d C
                   (@abelian_stability_preadditive C P t Ab) A B D pair)
                 T cone) e))
       (@computational_exact_cover_pullback_object C P t
         Ab A B D pair H T cone)
       (@Struct_sigma
         (Hom C
           (@computational_exact_cover_pullback_object C P t
             Ab A B D pair H T cone)
           T)
         (λ e : τ (Hom C
             (@computational_exact_cover_pullback_object C P t
               Ab A B D pair H T cone)
             T),
           `Σ_ epic : τ (@IsEpic C
             (@computational_exact_cover_pullback_object C P t
               Ab A B D pair H T cone)
             T e),
           `Σ_ a : τ (Hom C
             (@computational_exact_cover_pullback_object C P t
               Ab A B D pair H T cone)
             A),
             @= (Hom C
               (@computational_exact_cover_pullback_object C P t
                 Ab A B D pair H T cone)
               B)
               (@comp_fapp0 C _ _ _
                 (@computational_chain_pair_dnext C
                   (@abelian_stability_preadditive C P t Ab)
                   A B D pair) a)
               (@comp_fapp0 C _ _ _
                 (@weak_kernel_annihilator_arrow C
                   (@abelian_stability_preadditive C P t Ab)
                   B D
                   (@computational_chain_pair_d C
                     (@abelian_stability_preadditive C P t Ab) A B D pair)
                   T cone) e))
         (@computational_exact_cover_pullback_epi C P t
           Ab A B D pair H T cone)
         (@Struct_sigma
           (@IsEpic C
             (@computational_exact_cover_pullback_object C P t
               Ab A B D pair H T cone)
             T
             (@computational_exact_cover_pullback_epi C P t
               Ab A B D pair H T cone))
           (λ _ : τ _,
             `Σ_ a : τ (Hom C
               (@computational_exact_cover_pullback_object C P t
                 Ab A B D pair H T cone)
               A),
               @= (Hom C
                 (@computational_exact_cover_pullback_object C P t
                   Ab A B D pair H T cone)
                 B)
                 (@comp_fapp0 C _ _ _
                   (@computational_chain_pair_dnext C
                     (@abelian_stability_preadditive C P t Ab)
                     A B D pair) a)
                 (@comp_fapp0 C _ _ _
                   (@weak_kernel_annihilator_arrow C
                     (@abelian_stability_preadditive C P t Ab)
                     B D
                     (@computational_chain_pair_d C
                       (@abelian_stability_preadditive C P t Ab) A B D pair)
                     T cone)
                   (@computational_exact_cover_pullback_epi C P t
                     Ab A B D pair H T cone)))
           (@computational_exact_cover_pullback_is_epic C P t
             Ab A B D pair H exact T cone)
           (@Struct_sigma
             (Hom C
               (@computational_exact_cover_pullback_object C P t
                 Ab A B D pair H T cone)
               A)
             (λ a : τ (Hom C
                 (@computational_exact_cover_pullback_object C P t
                   Ab A B D pair H T cone)
                 A),
               @= (Hom C
                 (@computational_exact_cover_pullback_object C P t
                   Ab A B D pair H T cone)
                 B)
                 (@comp_fapp0 C _ _ _
                   (@computational_chain_pair_dnext C
                     (@abelian_stability_preadditive C P t Ab)
                     A B D pair) a)
                 (@comp_fapp0 C _ _ _
                   (@weak_kernel_annihilator_arrow C
                     (@abelian_stability_preadditive C P t Ab)
                     B D
                     (@computational_chain_pair_d C
                       (@abelian_stability_preadditive C P t Ab) A B D pair)
                     T cone)
                   (@computational_exact_cover_pullback_epi C P t
                     Ab A B D pair H T cone)))
             (@computational_exact_cover_pullback_factor C P t
               Ab A B D pair H T cone)
             (@computational_exact_cover_pullback_path C P t
               Ab A B D pair H T cone))));
