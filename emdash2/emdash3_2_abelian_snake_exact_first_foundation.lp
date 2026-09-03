/* First snake exactness position and its canonical-row local cover. */

require open emdash.emdash3_2_abelian_snake_six_term_kernel_zero;
require open emdash.emdash3_2_abelian_canonical_cokernel_covers;

symbol abelian_snake_first_exact_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalChainPair C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    (@abelian_snake_kernel_maps_zero_path C P t Ab A B X D triple);

symbol abelian_snake_first_exact_homology
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalHomologyAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_first_exact_pair C P t Ab A B X D triple))
≔ @computational_homology_at C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_first_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_first_row_cone
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
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      B
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      T)
≔ @Struct_sigma
    (Hom C T B)
    (λ h : τ (Hom C T B),
      @= (Hom C T
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _
          (@abelian_snake_epsilon C P t Ab A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab) T
          (@abelian_snake_coker_delta_object C P t Ab A B X D triple)))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_k_beta C P t Ab A B X D triple)
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        T cone))
    (@eq_trans _ _ _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_k_beta C P t Ab A B X D triple)
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
          T cone))
      (@eq_trans _ _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
          (Hom C T
            (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
          (λ h : τ (Hom C
              (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple)),
            @comp_fapp0 C _ _ _ h
              (@weak_kernel_annihilator_arrow C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                (@abelian_snake_ker_beta_to_ker_gamma C P t
                  Ab A B X D triple)
                T cone))
          _ _
          (@eq_sym _ _ _
            (@abelian_snake_ker_beta_to_ker_gamma_path C P t
              Ab A B X D triple)))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _
            (@comp_assoc C _ _ _ _
              (@abelian_snake_iota C P t Ab A B X D triple)
              (@abelian_snake_ker_beta_to_ker_gamma C P t
                Ab A B X D triple)
              (@weak_kernel_annihilator_arrow C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                (@abelian_snake_ker_beta_to_ker_gamma C P t
                  Ab A B X D triple)
                T cone)))
          (@eq_trans _ _ _ _
            (@eq_ap
              (Hom C T
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
              (Hom C T
                (@abelian_snake_coker_delta_object C P t Ab A B X D triple))
              (λ h : τ (Hom C T
                  (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
                @comp_fapp0 C _ _ _
                  (@abelian_snake_iota C P t Ab A B X D triple) h)
              _ _
              (@weak_kernel_annihilator_path C
                (@abelian_stability_preadditive C P t Ab)
                (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
                (@abelian_snake_ker_beta_to_ker_gamma C P t
                  Ab A B X D triple)
                T cone))
            (@preadditive_comp_zero_right_path C
              (@abelian_stability_preadditive C P t Ab)
              T
              (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
              (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
              (@abelian_snake_iota C P t Ab A B X D triple))))));

symbol abelian_snake_first_row_cover
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
      A B
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      (@abelian_canonical_cokernel_pair_explicit C P t
        (@abelian_stability_preabelian C P t Ab) A B
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple))
      T
      (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone))
≔ (@abelian_canonical_cokernel_covers_explicit C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    A B
    (@abelian_snake_delta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple))
    T
    (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone);
