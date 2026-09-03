/* Cancel the selected Ker(gamma) embedding after the cover calculation. */

require open emdash.emdash3_2_abelian_snake_exact_second_iota_comparison;

symbol abelian_snake_second_cover_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_second_alpha_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        (@abelian_snake_second_kernel_factor C P t
          Ab A B X D T triple cone))
      (@comp_fapp0 C _ _ _
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_connecting C P t Ab A B X D triple)
          T cone)
        (@comp_fapp0 C _ _ _
          (@abelian_snake_second_cover_epi C P t
            Ab A B X D T triple cone)
          (@abelian_snake_second_alpha_cover_epi C P t
            Ab A B X D T triple cone))))
≔ (@computational_kernel_morphism_is_monic C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    D
    (@abelian_snake_gamma C P t Ab A B X D triple)
    (@abelian_snake_gamma_kernel C P t Ab A B X D triple))
    (@abelian_snake_second_alpha_cover_object C P t
      Ab A B X D T triple cone)
    (@comp_fapp0 C _ _ _
      (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
      (@abelian_snake_second_kernel_factor C P t
        Ab A B X D T triple cone))
    (@comp_fapp0 C _ _ _
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple)
        T cone)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_second_cover_epi C P t
          Ab A B X D T triple cone)
        (@abelian_snake_second_alpha_cover_epi C P t
          Ab A B X D T triple cone)))
    (@abelian_snake_second_iota_cover_comparison_path C P t
      Ab A B X D T triple cone);
