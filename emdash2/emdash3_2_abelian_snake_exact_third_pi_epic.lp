/* Readable epicity of the selected cokernel projection pi. */

require open emdash.emdash3_2_abelian_snake_exact_third_pi_comparison;

symbol abelian_snake_third_pi_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  : τ (@IsEpic C (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple) (@abelian_snake_pi C P t Ab A B X D
    triple))
≔ @computational_cokernel_morphism_is_epic C (@abelian_stability_preadditive C P t Ab) A
  (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple) (@abelian_snake_alpha_cokernel C P t Ab A B X D
      triple);
