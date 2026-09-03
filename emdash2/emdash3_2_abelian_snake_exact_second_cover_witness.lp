/* One exact-cover witness at Ker(gamma). */

require open emdash.emdash3_2_abelian_snake_exact_second_total_cover;

symbol abelian_snake_second_exact_cover
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
  : τ (@ComputationalExactCoverWitness C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_second_exact_pair C P t Ab A B X D triple)
      T cone)
≔ @computational_exact_cover_intro C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_second_exact_pair C P t Ab A B X D triple)
    T cone
    (@abelian_snake_second_alpha_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_total_cover_epi C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_total_cover_is_epic C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_kernel_factor C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_cover_comparison_path C P t
      Ab A B X D T triple cone);
