/* Fiber-product factor used by the second snake zero composite. */

require open emdash.emdash3_2_abelian_snake_six_term_kernel_beta_foundation;

symbol abelian_snake_k_beta_fiber_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@FiberProductCone C P t
      (@abelian_stability_additive C P t Ab)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
      B
      (@abelian_snake_iota C P t Ab A B X D triple)
      (@abelian_snake_epsilon C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
≔ @fiber_product_cone_intro C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    B
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    (@abelian_snake_k_beta C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma_path C P t Ab A B X D triple);

symbol abelian_snake_k_beta_fiber_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_fiber_object C P t Ab A B X D triple))
≔ @computational_fiber_product_lift C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_k_beta_fiber_cone C P t Ab A B X D triple);

symbol abelian_snake_k_beta_fiber_lift_p1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_p1 C P t Ab A B X D triple)
        (@abelian_snake_k_beta_fiber_lift C P t Ab A B X D triple))
      (@abelian_snake_ker_beta_to_ker_gamma C P t
        Ab A B X D triple))
≔ @computational_fiber_product_lift_proj1_path C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_k_beta_fiber_cone C P t Ab A B X D triple);

symbol abelian_snake_k_beta_fiber_lift_p2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple) B)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_p2 C P t Ab A B X D triple)
        (@abelian_snake_k_beta_fiber_lift C P t Ab A B X D triple))
      (@abelian_snake_k_beta C P t Ab A B X D triple))
≔ @computational_fiber_product_lift_proj2_path C P t
    (@abelian_stability_additive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    B
    (@abelian_snake_iota C P t Ab A B X D triple)
    (@abelian_snake_epsilon C P t Ab A B X D triple)
    (@abelian_snake_fiber_product C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_k_beta_fiber_cone C P t Ab A B X D triple);
