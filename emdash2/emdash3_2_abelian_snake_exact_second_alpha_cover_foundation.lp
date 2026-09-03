/* Canonical cokernel-row cover of xi through alpha. */

require open emdash.emdash3_2_abelian_snake_exact_second_pi_zero;
require open emdash.emdash3_2_abelian_canonical_cokernel_covers;

symbol abelian_snake_second_alpha_pair
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@ComputationalChainPair C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple))
≔ @computational_chain_pair_intro C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_second_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_second_cover_xi C P t Ab A B X D T triple cone)
    (@abelian_snake_pi C P t Ab A B X D triple)
    (@abelian_snake_second_pi_xi_zero_path C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_alpha_cone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@WeakKernelAnnihilator C
      (@abelian_stability_preadditive C P t Ab)
      (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
      (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
      (@abelian_snake_pi C P t Ab A B X D triple)
      (@abelian_snake_second_cover_object C P t
        Ab A B X D T triple cone))
≔ @computational_chain_pair_cone C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_second_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_second_alpha_pair C P t
      Ab A B X D T triple cone);

symbol abelian_snake_second_alpha_cover
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X D T : τ (Obj C)]
  (triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D))
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_coker_alpha_object C P t Ab A B X D triple)
    (@abelian_snake_connecting C P t Ab A B X D triple)
    T))
  : τ (@ComputationalExactCoverWitness C P t
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
        Ab A B X D T triple cone))
≔ (@abelian_canonical_cokernel_covers_explicit C P t
    (@abelian_stability_preabelian C P t Ab)
    (@abelian_stability_mono_lifts C P t Ab)
    (@abelian_stability_epi_colifts C P t Ab)
    A
    (@abelian_snake_ker_lambda_object C P t Ab A B X D triple)
    (@abelian_snake_alpha C P t Ab A B X D triple))
    (@abelian_snake_second_cover_object C P t
      Ab A B X D T triple cone)
    (@abelian_snake_second_alpha_cone C P t
      Ab A B X D T triple cone);
