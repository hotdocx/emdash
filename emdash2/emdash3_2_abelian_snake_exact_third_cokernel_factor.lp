/* Descend the corrected difference through the selected Coker(beta). */

require open emdash.emdash3_2_abelian_snake_exact_third_beta_difference;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol abelian_snake_third_beta_difference_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple) T))
  : τ (@CokernelCoannihilator C (@abelian_stability_preadditive C P t Ab) B X (@abelian_snake_beta C
    (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
≔ @cokernel_zero_difference_cone C (@abelian_stability_preadditive C P t Ab) B X
  (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
    (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T
      triple cocone) (@comp_fapp0 C _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A
      B X D T triple cocone) (@abelian_snake_q1 C P t Ab A B X D triple)))
    (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_factor C P t Ab A B X D T triple
      cocone) (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D triple))
    (@abelian_snake_third_beta_coextensions_path C P t Ab A B X D T triple cocone);

symbol abelian_snake_third_cokernel_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple) T))
  : τ (Hom C (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
≔ @computational_cokernel_colift C (@abelian_stability_preadditive C P t Ab) B X
  (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
      (@abelian_snake_third_beta_difference_cocone C P t Ab A B X D T triple cocone);

symbol abelian_snake_third_cokernel_factor_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cocone : τ (@CokernelCoannihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple) T))
  : τ (@= (Hom C X (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _ (@abelian_snake_third_cokernel_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_c_beta C P t Ab A B X D triple))
      (@preadditive_hom_add C (@abelian_stability_preadditive C P t Ab) X
        (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone) (@comp_fapp0
        C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple cocone)
        (@comp_fapp0 C _ _ _ (@abelian_snake_third_extension_pushout_factor C P t Ab A B X D T
        triple cocone) (@abelian_snake_q1 C P t Ab A B X D triple)))
        (@preadditive_hom_neg C (@abelian_stability_preadditive C P t Ab) X
          (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
          (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_factor C P t Ab A B X D T
          triple cocone) (@abelian_snake_lambda C (@abelian_stability_preadditive C P t Ab) A B X D
          triple)))))
≔ @computational_cokernel_colift_path C (@abelian_stability_preadditive C P t Ab) B X
  (@abelian_snake_beta C (@abelian_stability_preadditive C P t Ab) A B X D triple)
    (@abelian_snake_beta_cokernel C P t Ab A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)
      (@abelian_snake_third_beta_difference_cocone C P t Ab A B X D T triple cocone);
