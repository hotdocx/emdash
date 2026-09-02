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

// Pullback stability supplies the epic projection used by CAP's colift.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_p1_epic C P t Ab A B X D triple
  : τ (@IsEpic C
      (@computational_fiber_product_object C P t
        (@abelian_stability_additive C P t Ab)
        (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
        (@abelian_snake_coker_delta_object C P t Ab A B X D triple) B
        (@abelian_snake_iota C P t Ab A B X D triple)
        (@abelian_snake_epsilon C P t Ab A B X D triple)
        (@abelian_snake_fiber_product C P t Ab A B X D triple))
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple));

// Pushout stability supplies the monic injection used by CAP's final lift.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_q2_monic C P t Ab A B X D triple
  : τ (@IsMonic C
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@computational_pushout_object C P t
        (@abelian_stability_additive C P t Ab)
        X (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
        (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
        (@abelian_snake_mu C P t Ab A B X D triple)
        (@abelian_snake_pi C P t Ab A B X D triple)
        (@abelian_snake_pushout C P t Ab A B X D triple))
      (@abelian_snake_q2 C P t Ab A B X D triple));
