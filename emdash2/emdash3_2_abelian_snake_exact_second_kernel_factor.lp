/* Factor the corrected B-valued lift through Ker(beta). */

require open emdash.emdash3_2_abelian_snake_exact_second_beta_difference;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_second_beta_difference_cone
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
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      B X
      (@abelian_snake_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_second_alpha_cover_object C P t
        Ab A B X D T triple cone))
≔ @kernel_zero_difference_cone C
    (@abelian_stability_preadditive C P t Ab)
    B X
    (@abelian_snake_second_alpha_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@comp_fapp0 C _ _ _
      (@comp_fapp0 C _ _ _
        (@abelian_snake_p2 C P t Ab A B X D triple)
        (@abelian_snake_second_cover_fiber_lift C P t
          Ab A B X D T triple cone))
      (@abelian_snake_second_alpha_cover_epi C P t
        Ab A B X D T triple cone))
    (@comp_fapp0 C _ _ _
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple)
      (@abelian_snake_second_alpha_cover_factor C P t
        Ab A B X D T triple cone))
    (@abelian_snake_second_beta_lifts_path C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_kernel_factor
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
  : τ (Hom C
      (@abelian_snake_second_alpha_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab)
    B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple)
    (@abelian_snake_second_alpha_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_beta_difference_cone C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_kernel_factor_path
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
      B)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_k_beta C P t Ab A B X D triple)
        (@abelian_snake_second_kernel_factor C P t
          Ab A B X D T triple cone))
      (@preadditive_hom_add C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_second_alpha_cover_object C P t
          Ab A B X D T triple cone)
        B
        (@comp_fapp0 C _ _ _
          (@comp_fapp0 C _ _ _
            (@abelian_snake_p2 C P t Ab A B X D triple)
            (@abelian_snake_second_cover_fiber_lift C P t
              Ab A B X D T triple cone))
          (@abelian_snake_second_alpha_cover_epi C P t
            Ab A B X D T triple cone))
        (@preadditive_hom_neg C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_second_alpha_cover_object C P t
            Ab A B X D T triple cone)
          B
          (@comp_fapp0 C _ _ _
            (@abelian_snake_delta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)
            (@abelian_snake_second_alpha_cover_factor C P t
              Ab A B X D T triple cone)))))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab)
    B X
    (@abelian_snake_beta C
      (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_kernel C P t Ab A B X D triple)
    (@abelian_snake_second_alpha_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_beta_difference_cone C P t
      Ab A B X D T triple cone);
