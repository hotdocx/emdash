/* First-row cover factor through Ker(alpha) and its reconstruction. */

require open emdash.emdash3_2_abelian_snake_exact_first_alpha_zero;

symbol abelian_snake_first_cover_alpha_cone
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
      A
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_alpha C P t Ab A B X D triple)
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone))
≔ @Struct_sigma
    (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      A)
    (λ h : τ (Hom C
        (@abelian_snake_first_row_cover_object C P t
          Ab A B X D T triple cone)
        A),
      @= (Hom C
        (@abelian_snake_first_row_cover_object C P t
          Ab A B X D T triple cone)
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _
          (@abelian_snake_alpha C P t Ab A B X D triple) h)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_first_row_cover_object C P t
            Ab A B X D T triple cone)
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)))
    (@abelian_snake_first_row_cover_factor C P t
      Ab A B X D T triple cone)
    (@abelian_snake_first_row_cover_alpha_zero_path C P t
      Ab A B X D T triple cone);

symbol abelian_snake_first_cover_kernel_factor
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
  : τ (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple))
≔ @computational_kernel_lift C
    (@abelian_stability_preadditive C P t Ab)
    A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_kernel C P t Ab A B X D triple)
    (@abelian_snake_first_row_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_first_cover_alpha_cone C P t
      Ab A B X D T triple cone);

symbol abelian_snake_first_cover_kernel_factor_path
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
  : τ (@= (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      A)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_k_alpha C P t Ab A B X D triple)
        (@abelian_snake_first_cover_kernel_factor C P t
          Ab A B X D T triple cone))
      (@abelian_snake_first_row_cover_factor C P t
        Ab A B X D T triple cone))
≔ @computational_kernel_lift_path C
    (@abelian_stability_preadditive C P t Ab)
    A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple)
    (@abelian_snake_alpha_kernel C P t Ab A B X D triple)
    (@abelian_snake_first_row_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_first_cover_alpha_cone C P t
      Ab A B X D T triple cone);
