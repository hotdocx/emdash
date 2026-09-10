/* Lift/colift centres retain the supplied all-test factors. */
require open emdash.emdash3_2_hom_factor_universality;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] [alpha : τ (Hom C A B)]
  (K : τ (Obj C)) (kappa : τ (Hom C K A))
  (zero : τ (@= (Hom C K B) (@comp_fapp0 C K A B alpha kappa)
    (@preadditive_hom_zero C S K B)))
  (monic : τ (@IsMonic C K A kappa))
  (factors : Π T : τ (Obj C), Π cone : τ (@WeakKernelAnnihilator C S A B alpha T),
    τ (@KernelFactorSpace C S A B alpha K kappa T cone))
  (T : τ (Obj C)) (cone : τ (@WeakKernelAnnihilator C S A B alpha T)) ⊢
  @computational_kernel_lift C S A B alpha
    (@computational_kernel_from_monic_factors C S A B alpha K kappa zero monic factors)
    T cone
  ≡ sigma_Fst (factors T cone);

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)] [alpha : τ (Hom C A B)]
  (Q : τ (Obj C)) (q : τ (Hom C B Q))
  (zero : τ (@= (Hom C A Q) (@comp_fapp0 C A B Q q alpha)
    (@preadditive_hom_zero C S A Q)))
  (epic : τ (@IsEpic C B Q q))
  (factors : Π T : τ (Obj C), Π cocone : τ (@CokernelCoannihilator C S A B alpha T),
    τ (@CokernelFactorSpace C S A B alpha Q q T cocone))
  (T : τ (Obj C)) (cocone : τ (@CokernelCoannihilator C S A B alpha T)) ⊢
  @computational_cokernel_colift C S A B alpha
    (@computational_cokernel_from_epic_factors C S A B alpha Q q zero epic factors)
    T cocone
  ≡ sigma_Fst (factors T cocone);
