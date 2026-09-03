/* Readable projections of the first canonical-row exactness cover. */

require open emdash.emdash3_2_abelian_snake_exact_first_foundation;

symbol abelian_snake_first_row_cover_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (Obj C)
≔ @computational_exact_cover_object C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_canonical_cokernel_pair_explicit C P t
      (@abelian_stability_preabelian C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    T
    (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone)
    (@abelian_snake_first_row_cover C P t Ab A B X D T triple cone);

symbol abelian_snake_first_row_cover_epi
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      T)
≔ @computational_exact_cover_epimorphism C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_canonical_cokernel_pair_explicit C P t
      (@abelian_stability_preabelian C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    T
    (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone)
    (@abelian_snake_first_row_cover C P t Ab A B X D T triple cone);

symbol abelian_snake_first_row_cover_is_epic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (@IsEpic C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      T
      (@abelian_snake_first_row_cover_epi C P t
        Ab A B X D T triple cone))
≔ @computational_exact_cover_is_epic C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_canonical_cokernel_pair_explicit C P t
      (@abelian_stability_preabelian C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    T
    (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone)
    (@abelian_snake_first_row_cover C P t Ab A B X D T triple cone);

symbol abelian_snake_first_row_cover_factor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      A)
≔ @computational_exact_cover_factor C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_canonical_cokernel_pair_explicit C P t
      (@abelian_stability_preabelian C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    T
    (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone)
    (@abelian_snake_first_row_cover C P t Ab A B X D T triple cone);

symbol abelian_snake_first_row_cover_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B X D T : τ (Obj C)]
  [triple : τ (@AbelianSnakeTriple C
    (@abelian_stability_preadditive C P t Ab) A B X D)]
  (cone : τ (@WeakKernelAnnihilator C
    (@abelian_stability_preadditive C P t Ab)
    (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
    (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
    (@abelian_snake_ker_beta_to_ker_gamma C P t Ab A B X D triple)
    T))
  : τ (@= (Hom C
      (@abelian_snake_first_row_cover_object C P t
        Ab A B X D T triple cone)
      B)
      (@comp_fapp0 C _ _ _
        (@abelian_snake_delta C
          (@abelian_stability_preadditive C P t Ab) A B X D triple)
        (@abelian_snake_first_row_cover_factor C P t
          Ab A B X D T triple cone))
      (@comp_fapp0 C _ _ _
        (@comp_fapp0 C _ _ _
          (@abelian_snake_k_beta C P t Ab A B X D triple)
          (@weak_kernel_annihilator_arrow C
            (@abelian_stability_preadditive C P t Ab)
            (@abelian_snake_ker_beta_object C P t Ab A B X D triple)
            (@abelian_snake_ker_gamma_object C P t Ab A B X D triple)
            (@abelian_snake_ker_beta_to_ker_gamma C P t
              Ab A B X D triple)
            T cone))
        (@abelian_snake_first_row_cover_epi C P t
          Ab A B X D T triple cone)))
≔ @computational_exact_cover_path C P t
    (@abelian_stability_preabelian C P t Ab)
    A B
    (@abelian_snake_coker_delta_object C P t Ab A B X D triple)
    (@abelian_canonical_cokernel_pair_explicit C P t
      (@abelian_stability_preabelian C P t Ab) A B
      (@abelian_snake_delta C
        (@abelian_stability_preadditive C P t Ab) A B X D triple))
    T
    (@abelian_snake_first_row_cone C P t Ab A B X D T triple cone)
    (@abelian_snake_first_row_cover C P t Ab A B X D T triple cone);
