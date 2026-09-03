/* Second snake exactness position and the first epic pullback cover. */

require open emdash.emdash3_2_abelian_snake_six_term_inner_kernel_zero;
require open emdash.emdash3_2_exactness_covers;

symbol abelian_snake_second_exact_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalChainPair C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    (@abelian_snake_connecting_after_kernel_map_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_second_exact_homology
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@ComputationalHomologyAt C P t
      (@abelian_stability_preabelian C P t Ab)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_second_exact_pair C P t Ab A B X D triple))
≔ @computational_homology_at C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_second_exact_pair C P t Ab A B X D triple);

symbol abelian_snake_second_cover_pullback
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
  : τ (@ComputationalFiberProduct C P t
      (@abelian_stability_additive C P t Ab)
      T
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@weak_kernel_annihilator_arrow C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple)
        T cone)
      (@abelian_snake_p1 C P t Ab A B X D triple))
≔ @abelian_selected_fiber_product C P t Ab
    T
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cone)
    (@abelian_snake_p1 C P t Ab A B X D triple);

symbol abelian_snake_second_cover_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (Obj C)
≔ @computational_fiber_product_object C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cone)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_second_cover_pullback C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_cover_epi
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (Hom C
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      T)
≔ @computational_fiber_product_proj1 C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cone)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_second_cover_pullback C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_cover_fiber_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (Hom C
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_fiber_object C P t Ab A B X D triple))
≔ @computational_fiber_product_proj2 C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cone)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_second_cover_pullback C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_cover_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@IsEpic C
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      T
      (@abelian_snake_second_cover_epi C P t
        Ab A B X D T triple cone))
≔ @abelian_fiber_product_epic_projection C P t Ab
    T
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cone)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_p1_epic C P t Ab A B X D triple);

symbol abelian_snake_second_cover_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@weak_kernel_annihilator_arrow C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_connecting C P t Ab A B X D triple)
          T cone)
        (@abelian_snake_second_cover_epi C P t
          Ab A B X D T triple cone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_p1 C P t Ab A B X D triple)
        (@abelian_snake_second_cover_fiber_lift C P t
          Ab A B X D T triple cone)))
≔ @computational_fiber_product_compatibility_path C P t
    (@abelian_stability_additive C P t Ab)
    T
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_fiber_object C P t Ab A B X D triple)
    (@weak_kernel_annihilator_arrow C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_connecting C P t Ab A B X D triple)
      T cone)
    (@abelian_snake_p1 C P t Ab A B X D triple)
    (@abelian_snake_second_cover_pullback C P t
      Ab A B X D T triple cone);
