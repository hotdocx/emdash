/* The selected pushout cofactor kills the snake middle arrow. */

require open emdash.emdash3_2_abelian_snake_six_term_inner_cokernel_cofactor;

symbol abelian_snake_c_beta_beta_after_p2_zero_path
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
          (@abelian_snake_c_beta C P t Ab A B X D triple)
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@abelian_snake_p2 C P t Ab A B X D triple))
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
      (Hom C B
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (Hom C
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (λ h : τ (Hom C B
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
        @comp_fapp0 C _ _ _ h
          (@abelian_snake_p2 C P t Ab A B X D triple))
      _ _
      (@abelian_snake_c_beta_beta_zero_path C P t Ab A B X D triple))
    (@preadditive_comp_zero_left_path C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      B
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_p2 C P t Ab A B X D triple));

symbol abelian_snake_cofactor_q1_beta_p2_zero_path
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
          (@comp_fapp0 C _ _ _
            (@abelian_snake_c_beta_pushout_cofactor C P t
              Ab A B X D triple)
            (@abelian_snake_q1 C P t Ab A B X D triple))
          (@abelian_snake_beta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple))
        (@abelian_snake_p2 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C X
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (Hom C
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (λ h : τ (Hom C X
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
        @comp_fapp0 C _ _ _
          (@comp_fapp0 C _ _ _ h
            (@abelian_snake_beta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple))
          (@abelian_snake_p2 C P t Ab A B X D triple))
      _ _
      (@abelian_snake_c_beta_pushout_cofactor_q1_reconstruction_path C P t
        Ab A B X D triple))
    (@abelian_snake_c_beta_beta_after_p2_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_cofactor_q1_beta_grouped_p2_zero_path
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
          (@abelian_snake_c_beta_pushout_cofactor C P t
            Ab A B X D triple)
          (@comp_fapp0 C _ _ _
            (@abelian_snake_q1 C P t Ab A B X D triple)
            (@abelian_snake_beta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple)))
        (@abelian_snake_p2 C P t Ab A B X D triple))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@eq_ap
      (Hom C B
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (Hom C
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (λ h : τ (Hom C B
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
        @comp_fapp0 C _ _ _ h
          (@abelian_snake_p2 C P t Ab A B X D triple))
      _ _
      (@comp_assoc C _ _ _ _
        (@abelian_snake_c_beta_pushout_cofactor C P t Ab A B X D triple)
        (@abelian_snake_q1 C P t Ab A B X D triple)
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)))
    (@abelian_snake_cofactor_q1_beta_p2_zero_path C P t
      Ab A B X D triple);

symbol abelian_snake_cofactor_expanded_middle_zero_path
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
        (@abelian_snake_c_beta_pushout_cofactor C P t
          Ab A B X D triple)
        (@comp_fapp0 C _ _ _
          (@comp_fapp0 C _ _ _
            (@abelian_snake_q1 C P t Ab A B X D triple)
            (@abelian_snake_beta C
              (@abelian_stability_preadditive C P t Ab) A B X D triple))
          (@abelian_snake_p2 C P t Ab A B X D triple)))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_fiber_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ @eq_trans _ _ _ _
    (@comp_assoc C _ _ _ _
      (@abelian_snake_c_beta_pushout_cofactor C P t Ab A B X D triple)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_q1 C P t Ab A B X D triple)
        (@abelian_snake_beta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple))
      (@abelian_snake_p2 C P t Ab A B X D triple))
    (@abelian_snake_cofactor_q1_beta_grouped_p2_zero_path C P t
      Ab A B X D triple);
