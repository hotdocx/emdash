/* Short exact rows retain their original objects and structural arrows. */
require open emdash.emdash3_2_short_exact_universal_records;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) ⊢
  @computational_kernel_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_kernel_record C P t Ab A B D pair short) ≡ A;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) ⊢
  @computational_kernel_morphism C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_kernel_record C P t Ab A B D pair short) ≡ (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair);

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  (T : τ (Obj C)) (cone : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T)) ⊢
  @computational_kernel_lift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_kernel_record C P t Ab A B D pair short) T cone
  ≡ @comp_fapp0 C T (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) A (@iso_evidence_from C A (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) (@short_exact_kernel_comparison_iso C P t Ab A B D pair short))
      (@computational_kernel_lift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@computational_homology_cycles C P t (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) T cone);


assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) ⊢
  @computational_cokernel_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_cokernel_record C P t Ab A B D pair short) ≡ D;

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) ⊢
  @computational_cokernel_morphism C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_cokernel_record C P t Ab A B D pair short) ≡ (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair);

assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair))
  (T : τ (Obj C)) (cocone : τ (@CokernelCoannihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) T)) ⊢
  @computational_cokernel_colift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_cokernel_record C P t Ab A B D pair short) T cocone
  ≡ @comp_fapp0 C D (@short_exact_cokernel_object C P t Ab A B D pair) T (@computational_cokernel_colift C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair) (@short_exact_incoming_cokernel C P t Ab A B D pair) T cocone) (@short_exact_cokernel_comparison_inverse C P t Ab A B D pair short);
