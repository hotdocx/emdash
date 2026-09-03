/* Whole six-object/five-arrow snake snapshot with all adjacent zeros. */

require open emdash.emdash3_2_abelian_snake_connecting_result;
require open emdash.emdash3_2_abelian_snake_six_term_kernels;
require open emdash.emdash3_2_abelian_snake_six_term_cokernels;
require open emdash.emdash3_2_abelian_snake_six_term_kernel_zero;
require open emdash.emdash3_2_abelian_snake_six_term_cokernel_zero;
require open emdash.emdash3_2_abelian_snake_six_term_inner_kernel_zero;
require open emdash.emdash3_2_abelian_snake_six_term_inner_cokernel_zero;

symbol AbelianSnakeSixTermZeroData
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (k01 : τ (Hom C
    (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)))
  (k12 : τ (Hom C
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)))
  (partial : τ (Hom C
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)))
  (c34 : τ (Hom C
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
  (c45 : τ (Hom C
    (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))
  : Grpd
≔ @Product_grpd
    (@= (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
      (@comp_fapp0 C _ _ _ k12 k01)
      (@preadditive_hom_zero C
        (@abelian_stability_preadditive C P t Ab)
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)))
    (@Product_grpd
      (@= (Hom C
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
        (@comp_fapp0 C _ _ _ partial k12)
        (@preadditive_hom_zero C
          (@abelian_stability_preadditive C P t Ab)
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)))
      (@Product_grpd
        (@= (Hom C
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
          (@comp_fapp0 C _ _ _ c34 partial)
          (@preadditive_hom_zero C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)))
        (@= (Hom C
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
          (@comp_fapp0 C _ _ _ c45 c34)
          (@preadditive_hom_zero C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)))));

symbol AbelianSnakeSixTermResult
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : Grpd
≔ `Σ_ connecting : τ (@AbelianSnakeConnectingResult C P t
      Ab A B X D triple),
   `Σ_ k01 : τ (Hom C
      (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)),
   `Σ_ k12 : τ (Hom C
      (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
   `Σ_ c34 : τ (Hom C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
   `Σ_ c45 : τ (Hom C
      (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
      (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
      @AbelianSnakeSixTermZeroData C P t Ab A B X D triple
        k01 k12
        (@abelian_snake_connecting_result_arrow C P t
          Ab A B X D triple connecting)
        c34 c45;

symbol abelian_snake_six_term_result
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@AbelianSnakeSixTermResult C P t Ab A B X D triple)
≔ @Struct_sigma
    (@AbelianSnakeConnectingResult C P t Ab A B X D triple)
    (λ connecting : τ (@AbelianSnakeConnectingResult C P t
        Ab A B X D triple),
      `Σ_ k01 : τ (Hom C
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)),
      `Σ_ k12 : τ (Hom C
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
      `Σ_ c34 : τ (Hom C
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
      `Σ_ c45 : τ (Hom C
        (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
        (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
        @AbelianSnakeSixTermZeroData C P t Ab A B X D triple
          k01 k12
          (@abelian_snake_connecting_result_arrow C P t
            Ab A B X D triple connecting)
          c34 c45)
    (@abelian_snake_connecting_result C P t Ab A B X D triple)
    (@Struct_sigma
      (Hom C
        (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_ker_beta_object C P t Ab A B X D triple))
      (λ k01 : τ (Hom C
          (@abelian_snake_ker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)),
        `Σ_ k12 : τ (Hom C
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
        `Σ_ c34 : τ (Hom C
          (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
        `Σ_ c45 : τ (Hom C
          (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
          @AbelianSnakeSixTermZeroData C P t Ab A B X D triple
            k01 k12
            (@abelian_snake_connecting C P t Ab A B X D triple)
            c34 c45)
      (@abelian_snake_ker_alpha_to_ker_beta C P t Ab A B X D triple)
      (@Struct_sigma
        (Hom C
          (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
          (@abelian_snake_ker_gamma_object C P t Ab A B X D triple))
        (λ k12 : τ (Hom C
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)),
          `Σ_ c34 : τ (Hom C
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
          `Σ_ c45 : τ (Hom C
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
            @AbelianSnakeSixTermZeroData C P t Ab A B X D triple
              (@abelian_snake_ker_alpha_to_ker_beta C P t
                Ab A B X D triple)
              k12
              (@abelian_snake_connecting C P t Ab A B X D triple)
              c34 c45)
        (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
        (@Struct_sigma
          (Hom C
            (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
            (@abelian_snake_coker_beta_object C P t Ab A B X D triple))
          (λ c34 : τ (Hom C
              (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple)),
            `Σ_ c45 : τ (Hom C
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
              @AbelianSnakeSixTermZeroData C P t Ab A B X D triple
                (@abelian_snake_ker_alpha_to_ker_beta C P t
                  Ab A B X D triple)
                (@abelian_snake_ker_beta_to_ker_gamma C P t
                  Ab A B X D triple)
                (@abelian_snake_connecting C P t Ab A B X D triple)
                c34 c45)
          (@abelian_snake_coker_alpha_to_coker_beta C P t
            Ab A B X D triple)
          (@Struct_sigma
            (Hom C
              (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
              (@abelian_snake_coker_gamma_object C P t Ab A B X D triple))
            (λ c45 : τ (Hom C
                (@abelian_snake_coker_beta_object C P t Ab A B X D triple)
                (@abelian_snake_coker_gamma_object C P t Ab A B X D triple)),
              @AbelianSnakeSixTermZeroData C P t Ab A B X D triple
                (@abelian_snake_ker_alpha_to_ker_beta C P t
                  Ab A B X D triple)
                (@abelian_snake_ker_beta_to_ker_gamma C P t
                  Ab A B X D triple)
                (@abelian_snake_connecting C P t Ab A B X D triple)
                (@abelian_snake_coker_alpha_to_coker_beta C P t
                  Ab A B X D triple)
                c45)
            (@abelian_snake_coker_beta_to_coker_gamma C P t
              Ab A B X D triple)
            (@Product_pair_grpd _ _
              (@abelian_snake_kernel_maps_zero_path C P t
                Ab A B X D triple)
              (@Product_pair_grpd _ _
                (@abelian_snake_connecting_after_kernel_map_zero_path C P t
                  Ab A B X D triple)
                (@Product_pair_grpd _ _
                  (@abelian_snake_cokernel_map_after_connecting_zero_path C P t
                    Ab A B X D triple)
                  (@abelian_snake_cokernel_maps_zero_path C P t
                    Ab A B X D triple))))))));
