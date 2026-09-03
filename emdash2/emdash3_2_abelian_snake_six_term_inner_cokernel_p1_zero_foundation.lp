/* Third snake composite vanishes after precomposition with epic p1. */

require open emdash.emdash3_2_abelian_snake_connecting;
require open emdash.emdash3_2_abelian_snake_six_term_inner_cokernel_middle_zero_foundation;

// The cokernel-side snake composite is the selected cofactor followed by u.
symbol abelian_snake_cokernel_composite_to_cofactor_u_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_coker_alpha_to_coker_beta C P t
          Ab A B X D triple)
        (@abelian_snake_connecting C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta_pushout_cofactor C P t
          Ab A B X D triple)
        (@abelian_snake_u C P t Ab A B X D triple)))
≔ @eq_trans
    (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
    _ _ _
    (@eq_ap
      (Hom C
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (λ h : τ (Hom C
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
        @comp_fapp0 C _ _ _ h
          (@abelian_snake_connecting C P t Ab A B X D triple))
      _ _
      (@eq_sym _ _ _
        (@abelian_snake_c_beta_pushout_cofactor_q2_reconstruction_path C P t
          Ab A B X D triple)))
    (@eq_trans
      (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_c_beta_pushout_cofactor C P t
            Ab A B X D triple)
          (@abelian_snake_q2 C P t Ab A B X D triple)
          (@abelian_snake_connecting C P t Ab A B X D triple)))
      (@eq_ap
        (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_pushout_object C P t Ab A B X D triple))
        (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
        (λ h : τ (Hom C
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple)),
          @comp_fapp0 C _ _ _
            (@abelian_snake_c_beta_pushout_cofactor C P t
              Ab A B X D triple) h)
        _ _
        (@abelian_snake_connecting_path C P t Ab A B X D triple)));
// Precomposing the cokernel-side composite with p1 therefore gives zero.
symbol abelian_snake_cokernel_composite_after_p1_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_coker_alpha_to_coker_beta C P t
            Ab A B X D triple)
          (@abelian_snake_connecting C P t Ab A B X D triple))
        (@abelian_snake_p1 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @eq_trans
    (Hom C
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
    _ _ _
    (@eq_ap
      (Hom C
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (Hom C
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (λ h : τ (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
        @comp_fapp0 C _ _ _ h
          (@abelian_snake_p1 C P t Ab A B X D triple))
      _ _
      (@abelian_snake_cokernel_composite_to_cofactor_u_path C P t
        Ab A B X D triple))
    (@eq_trans
      (Hom C
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C _ _ _ _
          (@abelian_snake_c_beta_pushout_cofactor C P t
            Ab A B X D triple)
          (@abelian_snake_u C P t Ab A B X D triple)
          (@abelian_snake_p1 C P t Ab A B X D triple)))
      (@eq_trans
        (Hom C
          (@abelian_snake_fiber_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
        _ _ _
        (@eq_ap
          (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_pushout_object C P t Ab A B X D triple))
          (Hom C
            (@abelian_snake_fiber_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
          (λ h : τ (Hom C
              (@abelian_snake_fiber_object C P t Ab A B X D triple)
              (@abelian_snake_pushout_object C P t Ab A B X D triple)),
            @comp_fapp0 C _ _ _
              (@abelian_snake_c_beta_pushout_cofactor C P t
                Ab A B X D triple) h)
          _ _
          (@abelian_snake_u_path C P t Ab A B X D triple))
        (@abelian_snake_cofactor_expanded_middle_zero_path C P t
          Ab A B X D triple)));
