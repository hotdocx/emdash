/* Readable projections of the whole six-term snake snapshot. */

require open emdash.emdash3_2_abelian_snake_six_term_result;

symbol abelian_snake_six_term_connecting_result
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@AbelianSnakeConnectingResult C P t Ab A B X D triple)
≔ sigma_Fst result;

symbol abelian_snake_six_term_first_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
≔ sigma_Fst (sigma_Snd result);

symbol abelian_snake_six_term_second_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
≔ sigma_Fst (sigma_Snd (sigma_Snd result));

symbol abelian_snake_six_term_connecting_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
≔ @abelian_snake_connecting_result_arrow C P t Ab A B X D triple
    (@abelian_snake_six_term_connecting_result C P t
      Ab A B X D triple result);

symbol abelian_snake_six_term_fourth_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd result)));

symbol abelian_snake_six_term_fifth_arrow
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (Hom C
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
≔ sigma_Fst
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd result))));

symbol abelian_snake_six_term_zero_data
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@AbelianSnakeSixTermZeroData C P t Ab A B X D triple
      (@abelian_snake_six_term_first_arrow C P t
        Ab A B X D triple result)
      (@abelian_snake_six_term_second_arrow C P t
        Ab A B X D triple result)
      (@abelian_snake_six_term_connecting_arrow C P t
        Ab A B X D triple result)
      (@abelian_snake_six_term_fourth_arrow C P t
        Ab A B X D triple result)
      (@abelian_snake_six_term_fifth_arrow C P t
        Ab A B X D triple result))
≔ sigma_Snd
    (sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd result))));

symbol abelian_snake_six_term_first_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_six_term_second_arrow C P t
          Ab A B X D triple result)
        (@abelian_snake_six_term_first_arrow C P t
          Ab A B X D triple result))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)))
≔ sigma_Fst (@abelian_snake_six_term_zero_data C P t
    Ab A B X D triple result);

symbol abelian_snake_six_term_second_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@= (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_six_term_connecting_arrow C P t
          Ab A B X D triple result)
        (@abelian_snake_six_term_second_arrow C P t
          Ab A B X D triple result))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)))
≔ sigma_Fst (sigma_Snd (@abelian_snake_six_term_zero_data C P t
    Ab A B X D triple result));

symbol abelian_snake_six_term_third_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@= (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_six_term_fourth_arrow C P t
          Ab A B X D triple result)
        (@abelian_snake_six_term_connecting_arrow C P t
          Ab A B X D triple result))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
≔ sigma_Fst (sigma_Snd (sigma_Snd
    (@abelian_snake_six_term_zero_data C P t
      Ab A B X D triple result)));

symbol abelian_snake_six_term_fourth_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (result : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple))
  : τ (@= (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _
        (@abelian_snake_six_term_fifth_arrow C P t
          Ab A B X D triple result)
        (@abelian_snake_six_term_fourth_arrow C P t
          Ab A B X D triple result))
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
≔ sigma_Snd (sigma_Snd (sigma_Snd
    (@abelian_snake_six_term_zero_data C P t
      Ab A B X D triple result)));
