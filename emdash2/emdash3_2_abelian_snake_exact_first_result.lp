/* Epimorphic covers and exactness at Ker(beta). */

require open emdash.emdash3_2_abelian_snake_exact_first_comparison;

symbol abelian_snake_first_exact_cover
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (@ComputationalExactCoverWitness C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_first_exact_pair C P t Ab A B X D triple)
      T cone)
≔ @Struct_sigma
    (Obj C)
    (λ U : τ (Obj C),
      `Σ_ e : τ (Hom C U T),
      `Σ_ epic : τ (@IsEpic C U T e),
      `Σ_ a : τ (Hom C U
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)),
        @= (Hom C U
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
          (@comp_fapp0 C _ _ _
            (@abelian_snake_ker_alpha_to_ker_beta C P t
              Ab A B X D triple) a)
          (@comp_fapp0 C _ _ _
            (@weak_kernel_annihilator_arrow C
              (@abelian_stability_preadditive C P t Ab)
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
              (@abelian_snake_ker_beta_to_ker_gamma C P t
                Ab A B X D triple)
              T cone)
            e))
    (@abelian_snake_first_row_cover_object C P t
      Ab A B X D T triple cone)
    (@Struct_sigma
      (Hom C
        (@abelian_snake_first_row_cover_object C P t
          Ab A B X D T triple cone)
        T)
      (λ e : τ (Hom C
          (@abelian_snake_first_row_cover_object C P t
            Ab A B X D T triple cone)
          T),
        `Σ_ epic : τ (@IsEpic C
          (@abelian_snake_first_row_cover_object C P t
            Ab A B X D T triple cone)
          T e),
        `Σ_ a : τ (Hom C
          (@abelian_snake_first_row_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)),
          @= (Hom C
            (@abelian_snake_first_row_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
            (@comp_fapp0 C _ _ _
              (@abelian_snake_ker_alpha_to_ker_beta C P t
                Ab A B X D triple) a)
            (@comp_fapp0 C _ _ _
              (@weak_kernel_annihilator_arrow C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                (@abelian_snake_ker_beta_to_ker_gamma C P t
                  Ab A B X D triple)
                T cone)
              e))
      (@abelian_snake_first_row_cover_epi C P t
        Ab A B X D T triple cone)
      (@Struct_sigma
        (@IsEpic C
          (@abelian_snake_first_row_cover_object C P t
            Ab A B X D T triple cone)
          T
          (@abelian_snake_first_row_cover_epi C P t
            Ab A B X D T triple cone))
        (λ _ : τ _,
          `Σ_ a : τ (Hom C
            (@abelian_snake_first_row_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)),
            @= (Hom C
              (@abelian_snake_first_row_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
              (@comp_fapp0 C _ _ _
                (@abelian_snake_ker_alpha_to_ker_beta C P t
                  Ab A B X D triple) a)
              (@comp_fapp0 C _ _ _
                (@weak_kernel_annihilator_arrow C
                  (@abelian_stability_preadditive C P t Ab)
                  (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                  (@abelian_snake_ker_beta_to_ker_gamma C P t
                    Ab A B X D triple)
                  T cone)
                (@abelian_snake_first_row_cover_epi C P t
                  Ab A B X D T triple cone)))
        (@abelian_snake_first_row_cover_is_epic C P t
          Ab A B X D T triple cone)
        (@Struct_sigma
          (Hom C
            (@abelian_snake_first_row_cover_object C P t
              Ab A B X D T triple cone)
            (@abelian_snake_ker_alpha_object C P t Ab A B X D triple))
          (λ a : τ (Hom C
              (@abelian_snake_first_row_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)),
            @= (Hom C
              (@abelian_snake_first_row_cover_object C P t
                Ab A B X D T triple cone)
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
              (@comp_fapp0 C _ _ _
                (@abelian_snake_ker_alpha_to_ker_beta C P t
                  Ab A B X D triple) a)
              (@comp_fapp0 C _ _ _
                (@weak_kernel_annihilator_arrow C
                  (@abelian_stability_preadditive C P t Ab)
                  (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                  (@abelian_snake_ker_beta_to_ker_gamma C P t
                    Ab A B X D triple)
                  T cone)
                (@abelian_snake_first_row_cover_epi C P t
                  Ab A B X D T triple cone)))
          (@abelian_snake_first_cover_kernel_factor C P t
            Ab A B X D T triple cone)
          (@abelian_snake_first_cover_comparison_path C P t
            Ab A B X D T triple cone))));

symbol abelian_snake_first_exact_covers
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@HasComputationalExactCovers C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_first_exact_pair C P t Ab A B X D triple))
≔ λ T : τ (Obj C),
   λ cone : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
      T),
     @abelian_snake_first_exact_cover C P t
       Ab A B X D T triple cone;

symbol abelian_snake_exact_at_ker_beta
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalExactAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_first_exact_pair C P t Ab A B X D triple)
      (@abelian_snake_first_exact_homology C P t Ab A B X D triple))
≔ @computational_exact_at_from_covers C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_first_exact_pair C P t Ab A B X D triple)
    (@abelian_snake_first_exact_homology C P t Ab A B X D triple)
    (@abelian_snake_first_exact_covers C P t Ab A B X D triple);
