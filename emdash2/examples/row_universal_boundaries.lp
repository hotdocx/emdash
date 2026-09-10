/* Runtime boundaries, not claims that isomorphic objects or unique factors differ. */
require open emdash.emdash3_2_short_exact_universal_records;

// Row source A is not runtime-replaced by the independently selected kernel object.
assertnot [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) ⊢
  @computational_kernel_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_kernel_record C P t Ab A B D pair short)
  ≡ @computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) A B D pair
      (@computational_homology_at C P t (@computational_abelian_preabelian C P t Ab) A B D pair);

// Row target D is not runtime-replaced by the independently selected cokernel object.
assertnot [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t (@computational_abelian_preabelian C P t Ab) A B D pair)) ⊢
  @computational_cokernel_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B D pair)
    (@short_exact_cokernel_record C P t Ab A B D pair short)
  ≡ @short_exact_cokernel_object C P t Ab A B D pair;

// Cancellation proves uniqueness; it does not erase which factor term was supplied.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] [alpha : τ (Hom C A B)]
  (K : τ (Obj C)) (kappa : τ (Hom C K A))
  (zero : τ (@= (Hom C K B) (@comp_fapp0 C K A B alpha kappa) (@preadditive_hom_zero C S K B)))
  (monic : τ (@IsMonic C K A kappa))
  (factors other : Π T : τ (Obj C), Π cone : τ (@WeakKernelAnnihilator C S A B alpha T), τ (@KernelFactorSpace C S A B alpha K kappa T cone))
  (T : τ (Obj C)) (cone : τ (@WeakKernelAnnihilator C S A B alpha T)) ⊢
  @computational_kernel_lift C S A B alpha
    (@computational_kernel_from_monic_factors C S A B alpha K kappa zero monic factors) T cone
  ≡ @computational_kernel_lift C S A B alpha
      (@computational_kernel_from_monic_factors C S A B alpha K kappa zero monic other) T cone;

assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] [alpha : τ (Hom C A B)]
  (Q : τ (Obj C)) (q : τ (Hom C B Q))
  (zero : τ (@= (Hom C A Q) (@comp_fapp0 C A B Q q alpha) (@preadditive_hom_zero C S A Q)))
  (epic : τ (@IsEpic C B Q q))
  (factors other : Π T : τ (Obj C), Π cocone : τ (@CokernelCoannihilator C S A B alpha T), τ (@CokernelFactorSpace C S A B alpha Q q T cocone))
  (T : τ (Obj C)) (cocone : τ (@CokernelCoannihilator C S A B alpha T)) ⊢
  @computational_cokernel_colift C S A B alpha
    (@computational_cokernel_from_epic_factors C S A B alpha Q q zero epic factors) T cocone
  ≡ @computational_cokernel_colift C S A B alpha
      (@computational_cokernel_from_epic_factors C S A B alpha Q q zero epic other) T cocone;
