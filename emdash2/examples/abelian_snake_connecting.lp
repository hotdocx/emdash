/* Reviewer-facing generic Abelian snake connecting consumers. */

require open emdash.emdash3_2_abelian_snake_connecting_result;

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_p1_normal_epi_test C P t Ab A B X D triple
  : τ (@NormalEpiTest C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_fiber_object C P t Ab A B X D triple)
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_p1 C P t Ab A B X D triple)
      (@abelian_snake_p1_kernel C P t Ab A B X D triple)
      (@abelian_snake_pushout_object C P t Ab A B X D triple));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_connecting C P t Ab A B X D triple
  : τ (Hom C
      (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A B X D : τ (Obj C))
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  ⊢ @abelian_snake_connecting_result C P t Ab A B X D triple
  : τ (@AbelianSnakeConnectingResult C P t Ab A B X D triple);
