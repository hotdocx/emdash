/* Original short exact rows as universal kernel/cokernel records.
   The row objects and arrows are the operational fields, not equality casts
   of separately selected objects. Actual comparisons construct all-test factors. */
/* A short exact row presents its own source as the universal kernel.
   The inverse comparison is a genuine arrow, not an equality cast of objects. */
require open emdash.emdash3_2_short_exact_kernel_comparison;
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_hom_factor_universality;
require open emdash.emdash3_2_iso_comparison_reconstruction;

symbol short_exact_kernel_inverse_reconstruction
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@= (Hom C (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) B) (@comp_fapp0 C (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@iso_evidence_from C A (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) (@short_exact_kernel_comparison_iso C P t Ab A B D pair short))) (@computational_homology_cycle_embedding C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)))
≔ @iso_source_comparison_reverse_path C A (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@computational_homology_cycle_embedding C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) (@short_exact_kernel_comparison_iso C P t Ab A B D pair short)
    (@eq_sym _ _ _ (@computational_homology_boundary_path C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)));

symbol short_exact_kernel_factor
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  (T : τ (Obj C)) (cone : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T))
  : τ (@KernelFactorSpace C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) A (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T cone)
≔ @Struct_sigma (Hom C T A)
    (λ f : τ (Hom C T A), @= (Hom C T B) (@comp_fapp0 C T A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) f) (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T cone))
    (@comp_fapp0 C T (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) A (@iso_evidence_from C A (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) (@short_exact_kernel_comparison_iso C P t Ab A B D pair short)) (@computational_kernel_lift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@computational_homology_cycles C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) T cone))
    (@hom_factor_paste_path C T B (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) B A B
      (@weak_kernel_annihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T cone) (@computational_homology_cycle_embedding C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@computational_kernel_lift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@computational_homology_cycles C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) T cone) (@iso_evidence_from C A (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) (@short_exact_kernel_comparison_iso C P t Ab A B D pair short)) (@id C B) (@id C B)
      (@computational_kernel_lift_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@computational_homology_cycles C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) T cone)
      (@short_exact_kernel_inverse_reconstruction C P t Ab A B D pair short));

symbol short_exact_kernel_record
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@ComputationalKernel C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
≔ @computational_kernel_from_monic_factors C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) A (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@computational_chain_pair_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@computational_short_exact_monic C P t (@computational_abelian_preabelian C P t Ab) A B D pair short)
    (@short_exact_kernel_factor C P t Ab A B D pair short);

/* A short exact row presents its own target as the universal cokernel. */
require open emdash.emdash3_2_short_exact_cokernel_comparison;

symbol short_exact_cokernel_factor
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  (T : τ (Obj C)) (cocone : τ (@CokernelCoannihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T))
  : τ (@CokernelFactorSpace C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T cocone)
≔ @Struct_sigma (Hom C D T)
    (λ f : τ (Hom C D T), @= (Hom C B T) (@comp_fapp0 C B D T f (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)) (@cokernel_coannihilator_arrow C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T cocone))
    (@comp_fapp0 C D (@short_exact_cokernel_object C P t Ab A B D pair) T (@computational_cokernel_colift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@short_exact_incoming_cokernel C P t Ab A B D pair) T cocone) (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C B D (@short_exact_cokernel_object C P t Ab A B D pair) T (@computational_cokernel_colift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@short_exact_incoming_cokernel C P t Ab A B D pair) T cocone) (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short) (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair)) (Hom C B T)
          (λ h : τ (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair)), @comp_fapp0 C B (@short_exact_cokernel_object C P t Ab A B D pair) T (@computational_cokernel_colift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@short_exact_incoming_cokernel C P t Ab A B D pair) T cocone) h)
          _ _ (@short_exact_cokernel_comparison_inverse_path C P t Ab A B D pair short))
        (@computational_cokernel_colift_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@short_exact_incoming_cokernel C P t Ab A B D pair) T cocone)));

symbol short_exact_cokernel_record
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@ComputationalCokernel C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair))
≔ @computational_cokernel_from_epic_factors C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@computational_chain_pair_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@computational_short_exact_epic C P t (@computational_abelian_preabelian C P t Ab) A B D pair short)
    (@short_exact_cokernel_factor C P t Ab A B D pair short);
