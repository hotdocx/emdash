/* Cancel the selected epic pi in the extension reconstruction. */

require open emdash.emdash3_2_abelian_snake_exact_third_pi_epic;

symbol abelian_snake_third_extension_comparison_path
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
  : τ (@= (Hom C (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone))
      (@comp_fapp0 C _ _ _ (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C
        P t Ab A B X D T triple cocone) (@abelian_snake_third_extension_monomorphism C P t Ab A B X
        D T triple cocone)) (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P t
        Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone))
      (@comp_fapp0 C _ _ _ (@abelian_snake_third_cokernel_factor C P t Ab A B X D T triple cocone)
        (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)))
≔ @eq_sym (Hom C (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
  (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone)) (@comp_fapp0 C _ _
  _ (@abelian_snake_third_cokernel_factor C P t Ab A B X D T triple cocone)
  (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)) (@comp_fapp0 C _ _ _
  (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T triple
  cocone) (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone))
  (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone))
    ((@abelian_snake_third_pi_epic C P t Ab A B X D triple)
      (@abelian_snake_third_gamma_extension_object C P t Ab A B X D T triple cocone) (@comp_fapp0 C
      _ _ _ (@abelian_snake_third_cokernel_factor C P t Ab A B X D T triple cocone)
      (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)) (@comp_fapp0 C _ _ _
      (@comp_fapp0 C _ _ _ (@abelian_snake_third_gamma_extension_monomorphism C P t Ab A B X D T
      triple cocone) (@abelian_snake_third_extension_monomorphism C P t Ab A B X D T triple cocone))
      (@cokernel_coannihilator_arrow C (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple) (@abelian_snake_coker_alpha_object C P
      t Ab A B X D triple) (@abelian_snake_connecting C P t Ab A B X D triple) T cocone))
      (@abelian_snake_third_pi_comparison_path C P t Ab A B X D T triple cocone));
