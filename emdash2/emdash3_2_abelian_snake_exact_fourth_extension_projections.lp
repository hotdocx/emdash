/* Readable observations of the selected lambda-row extension. */

require open emdash.emdash3_2_abelian_snake_exact_fourth_extension;

symbol abelian_snake_fourth_extension_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ (Obj C)
≔ @computational_exact_extension_object C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X D
  (@abelian_canonical_kernel_pair_explicit C P t
    (@abelian_stability_preabelian C P t Ab) X D
    (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
  T
  (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_lambda_extension C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_extension_monomorphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ (Hom C T (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
≔ @computational_exact_extension_monomorphism C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X D
  (@abelian_canonical_kernel_pair_explicit C P t
    (@abelian_stability_preabelian C P t Ab) X D
    (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
  T
  (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_lambda_extension C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_extension_is_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@IsMonic C T
      (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone)
      (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone))
≔ @computational_exact_extension_is_monic C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X D
  (@abelian_canonical_kernel_pair_explicit C P t
    (@abelian_stability_preabelian C P t Ab) X D
    (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
  T
  (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_lambda_extension C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_extension_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ (Hom C D (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
≔ @computational_exact_extension_factor C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X D
  (@abelian_canonical_kernel_pair_explicit C P t
    (@abelian_stability_preabelian C P t Ab) X D
    (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
  T
  (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_lambda_extension C P t Ab A B X D T triple cocone);

symbol abelian_snake_fourth_extension_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    T))
  : τ
    (@=
      (Hom C X (@abelian_snake_fourth_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_fourth_extension_monomorphism C P t Ab A B X D T triple cocone)
        (@comp_fapp0 C _ _ _
          (@cokernel_coannihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple) T cocone)
          (@abelian_snake_c_beta C P t Ab A B X D triple)))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_fourth_extension_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple)))
≔ @computational_exact_extension_path C P t
  (@abelian_stability_preabelian C P t Ab)
  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple) X D
  (@abelian_canonical_kernel_pair_explicit C P t
    (@abelian_stability_preabelian C P t Ab) X D
    (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
  T
  (@abelian_snake_fourth_lambda_cocone C P t Ab A B X D T triple cocone)
  (@abelian_snake_fourth_lambda_extension C P t Ab A B X D T triple cocone);
