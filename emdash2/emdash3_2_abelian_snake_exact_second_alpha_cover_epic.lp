/* Epicity projection of the canonical alpha-row cover. */

require open emdash.emdash3_2_abelian_snake_exact_second_alpha_cover_epi;

symbol abelian_snake_second_alpha_cover_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@IsEpic C
      (@abelian_snake_second_alpha_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_second_alpha_cover_epi C P t
        Ab A B X D T triple cone))
≔ @computational_exact_cover_is_epic C P t
    (@abelian_stability_preabelian C P t Ab)
    A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_canonical_cokernel_pair_explicit C P t
      (@abelian_stability_preabelian C P t Ab)
      A
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_alpha C P t Ab A B X D triple))
    (@abelian_snake_second_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_alpha_cone C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_alpha_cover C P t
      Ab A B X D T triple cone);
