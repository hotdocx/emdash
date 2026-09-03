/* Pushout cofactor used by the third snake zero composite. */

require open emdash.emdash3_2_abelian_snake_six_term_cokernel_beta_foundation;

symbol abelian_snake_c_beta_pushout_cocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@PushoutCocone C P t
      (@abelian_stability_additive C P t Ab)
      X
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_mu C P t Ab A B X D triple)
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @pushout_cocone_intro C P t
    (@abelian_stability_additive C P t Ab)
    X
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_c_beta C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_to_coker_beta C P t Ab A B X D triple)
    (@eq_sym _ _ _
      (@abelian_snake_coker_alpha_to_coker_beta_path C P t
        Ab A B X D triple));

symbol abelian_snake_c_beta_pushout_cofactor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (Hom C
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t Ab)
        X
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_pushout C P t Ab A B X D triple))
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ @computational_pushout_cofactor C P t
    (@abelian_stability_additive C P t Ab)
    X
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_c_beta_pushout_cocone C P t Ab A B X D triple);

symbol abelian_snake_c_beta_pushout_cofactor_q1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C X
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta_pushout_cofactor C P t
          Ab A B X D triple)
        (@computational_pushout_inj1 C P t
          (@abelian_stability_additive C P t Ab)
          X
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_mu C P t Ab A B X D triple)
          (@abelian_snake_pi C P t Ab A B X D triple)
          (@abelian_snake_pushout C P t Ab A B X D triple)))
      (@pushout_cocone_inj1 C P t
        (@abelian_stability_additive C P t Ab)
        X
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_c_beta_pushout_cocone C P t Ab A B X D triple)))
≔ @computational_pushout_cofactor_inj1_path C P t
    (@abelian_stability_additive C P t Ab)
    X
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_c_beta_pushout_cocone C P t Ab A B X D triple);

symbol abelian_snake_c_beta_pushout_cofactor_q2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta_pushout_cofactor C P t
          Ab A B X D triple)
        (@computational_pushout_inj2 C P t
          (@abelian_stability_additive C P t Ab)
          X
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_mu C P t Ab A B X D triple)
          (@abelian_snake_pi C P t Ab A B X D triple)
          (@abelian_snake_pushout C P t Ab A B X D triple)))
      (@pushout_cocone_inj2 C P t
        (@abelian_stability_additive C P t Ab)
        X
        (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_c_beta_pushout_cocone C P t Ab A B X D triple)))
≔ @computational_pushout_cofactor_inj2_path C P t
    (@abelian_stability_additive C P t Ab)
    X
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_mu C P t Ab A B X D triple)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_pushout C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_c_beta_pushout_cocone C P t Ab A B X D triple);

// Readable first reconstruction: v o q1 = c_beta.
symbol abelian_snake_c_beta_pushout_cofactor_q1_reconstruction_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C X
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta_pushout_cofactor C P t
          Ab A B X D triple)
        (@computational_pushout_inj1 C P t
          (@abelian_stability_additive C P t Ab)
          X
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_mu C P t Ab A B X D triple)
          (@abelian_snake_pi C P t Ab A B X D triple)
          (@abelian_snake_pushout C P t Ab A B X D triple)))
      (@abelian_snake_c_beta C P t Ab A B X D triple))
≔ @eq_trans _ _ _ _
    (@abelian_snake_c_beta_pushout_cofactor_q1_path C P t
      Ab A B X D triple)
    (@additive_copair_inj1_path C P t
      (@abelian_stability_additive C P t Ab)
      X
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_c_beta C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_to_coker_beta C P t
        Ab A B X D triple));

// Readable second reconstruction: v o q2 = Coker(alpha) -> Coker(beta).
symbol abelian_snake_c_beta_pushout_cofactor_q2_reconstruction_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@= (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_c_beta_pushout_cofactor C P t
          Ab A B X D triple)
        (@computational_pushout_inj2 C P t
          (@abelian_stability_additive C P t Ab)
          X
          (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_mu C P t Ab A B X D triple)
          (@abelian_snake_pi C P t Ab A B X D triple)
          (@abelian_snake_pushout C P t Ab A B X D triple)))
      (@abelian_snake_coker_alpha_to_coker_beta C P t
        Ab A B X D triple))
≔ @eq_trans _ _ _ _
    (@abelian_snake_c_beta_pushout_cofactor_q2_path C P t
      Ab A B X D triple)
    (@additive_copair_inj2_path C P t
      (@abelian_stability_additive C P t Ab)
      X
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_c_beta C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_to_coker_beta C P t
        Ab A B X D triple));
