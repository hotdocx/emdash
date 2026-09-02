/* Reviewer-facing generic Abelian snake universal-construction spine. */

require open emdash.emdash3_2_abelian_snake_lemma;

// The first CAP factor is the selected map gamma : Coker(delta) -> D.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_gamma C P t Ab A B X D triple
  : τ (Hom C
      (@computational_cokernel_object C
        (@abelian_stability_preadditive C P t Ab) A B
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D);

// Its selected cokernel colift reconstructs lambda o beta.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_gamma_path C P t Ab A B X D triple
  : τ (@= (Hom C B D)
      (@comp_fapp0 C B
        (@computational_cokernel_object C
          (@abelian_stability_preadditive C P t Ab) A B
          (@abelian_snake_delta C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_delta_cokernel C P t Ab A B X D triple)) D
        (@abelian_snake_gamma C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple))
      (@abelian_snake_lambda_beta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple));

// The second CAP factor is alpha : A -> Ker(lambda).
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_alpha C P t Ab A B X D triple
  : τ (Hom C A
      (@computational_kernel_object C
        (@abelian_stability_preadditive C P t Ab) X D
        (@abelian_snake_lambda C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_lambda_kernel C P t Ab A B X D triple)));

// Its selected kernel lift reconstructs beta o delta.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_alpha_path C P t Ab A B X D triple
  : τ (@= (Hom C A X)
      (@comp_fapp0 C A
        (@computational_kernel_object C
          (@abelian_stability_preadditive C P t Ab) X D
          (@abelian_snake_lambda C
            (@abelian_stability_preadditive C P t Ab) A B X D triple)
          (@abelian_snake_lambda_kernel C P t Ab A B X D triple)) X
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_alpha C P t Ab A B X D triple))
      (@abelian_snake_beta_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple));
