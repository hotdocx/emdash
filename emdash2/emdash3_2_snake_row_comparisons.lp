/*
  Compare the canonical snake side maps with the end components of a row map.

  A common literal PA and its normality capabilities keep all selected
  kernel/cokernel owners aligned. Short exactness is only needed later to
  make the two row comparison arrows isomorphisms.
*/
require open emdash.emdash3_2_chain_pair_map_snake;
require open emdash.emdash3_2_short_exact_cokernel_foundation;

// (prev ∘ q_top) ∘ epsilon = lambda ∘ beta.
symbol snake_row_gamma_after_epsilon
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C B0 D1)
      (@comp_fapp0 C B0 (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D1 (@comp_fapp0 C (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@short_exact_cokernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0)) (@abelian_snake_epsilon C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
      (@comp_fapp0 C B0 B1 D1 (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 p1) (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
≔ (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C B0 (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@short_exact_cokernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) (@abelian_snake_epsilon C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C B0 D0) (Hom C B0 D1)
        (λ h : τ (Hom C B0 D0), @comp_fapp0 C B0 D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) h)
        _ _ (@short_exact_cokernel_comparison_path C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0))
      (@computational_chain_pair_map_lower_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)));

// gamma = prev(F) ∘ q_top by the actual incoming cokernel's uniqueness.
symbol snake_row_gamma_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D1) (@abelian_snake_gamma C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@comp_fapp0 C (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@short_exact_cokernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0)))
≔ @computational_cokernel_colift_unique_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 p0)
    (@abelian_snake_delta_cokernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) D1 (@abelian_snake_gamma_cone C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))
    (@comp_fapp0 C (@short_exact_cokernel_object C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0) D0 D1 (@computational_chain_pair_map_prev C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@short_exact_cokernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 D0 p0)) (@snake_row_gamma_after_epsilon C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F);

// mu ∘ (a_bottom ∘ next(F)) = beta ∘ delta.
symbol snake_row_alpha_after_mu
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C A0 B1)
      (@comp_fapp0 C A0 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) B1 (@abelian_snake_mu C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@comp_fapp0 C A0 A1 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) (@short_exact_kernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
      (@comp_fapp0 C A0 B0 B1 (@computational_chain_pair_map_middle C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F) (@computational_chain_pair_dnext C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 p0)))
≔ (@eq_trans _ _ _ _
      (@comp_assoc C A0 A1 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) B1 (@abelian_snake_mu C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@short_exact_kernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A1 B1) (Hom C A0 B1)
        (λ h : τ (Hom C A1 B1), @comp_fapp0 C A0 A1 B1 h (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))
        _ _ (@computational_homology_boundary_path C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)))
      (@computational_chain_pair_map_upper_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)));

// alpha = a_bottom ∘ next(F) by the actual outgoing kernel's uniqueness.
symbol snake_row_alpha_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  (M : τ (@HasLiftsAlongMonomorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_cokernels C P t PA)))
  (E : τ (@HasColiftsAlongEpimorphisms C (@additive_preadditive C P t (@preabelian_additive C P t PA)) (@preabelian_kernels C P t PA)))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1))
  (F : τ (@ComputationalChainPairMap C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C A0 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1))) (@abelian_snake_alpha C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@comp_fapp0 C A0 A1 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) (@short_exact_kernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)))
≔ @computational_kernel_lift_unique_path C (@additive_preadditive C P t (@preabelian_additive C P t PA)) B1 D1 (@computational_chain_pair_d C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A1 B1 D1 p1)
    (@abelian_snake_lambda_kernel C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) A0 (@abelian_snake_alpha_cone C P t (@computational_abelian_category_intro C P t PA M E) A0 B0 B1 D1 (@chain_pair_map_snake_triple C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F))
    (@comp_fapp0 C A0 A1 (@computational_homology_cycle_object C P t PA A1 B1 D1 p1 (@computational_homology_at C P t PA A1 B1 D1 p1)) (@short_exact_kernel_comparison C P t (@computational_abelian_category_intro C P t PA M E) A1 B1 D1 p1) (@computational_chain_pair_map_next C (@additive_preadditive C P t (@preabelian_additive C P t PA)) A0 B0 D0 A1 B1 D1 p0 p1 F)) (@snake_row_alpha_after_mu C P t PA M E A0 B0 D0 A1 B1 D1 p0 p1 F);
