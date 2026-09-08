/* The inverse comparison, not a new selection of kernel or arrow. */
require open emdash.emdash3_2_kernel_domain_comparison_factors;

assert
  (C : Cat) (S : τ (@PreadditiveCategory C)) (A0 A1 B : τ (Obj C))
  (d0 : τ (Hom C A0 B)) (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0
    (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  ⊢ (@hom_postcomp_factor_arrow C (@computational_kernel_object C S A0 B d0 K0) A1 (@computational_kernel_object C S A1 B d1 K1) (@comp_fapp0 C (@computational_kernel_object C S A0 B d0 K0) A0 A1 (@iso_evidence_to C A0 A1 iso) (@computational_kernel_morphism C S A0 B d0 K0)) (@computational_kernel_morphism C S A1 B d1 K1) (@kernel_domain_comparison_source_factor C S A0 A1 B d0 d1 K0 K1 iso comparison)) ≡ (@iso_evidence_from C (@computational_kernel_object C S A0 B d0 K0) (@computational_kernel_object C S A1 B d1 K1) (@kernel_domain_comparison_iso C S A0 A1 B d0 d1 K0 K1 iso comparison));

assert
  (C : Cat) (S : τ (@PreadditiveCategory C)) (A0 A1 B : τ (Obj C))
  (d0 : τ (Hom C A0 B)) (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0
    (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  ⊢ @hom_postcomp_factor_path C (@computational_kernel_object C S A0 B d0 K0) A1 (@computational_kernel_object C S A1 B d1 K1) (@comp_fapp0 C (@computational_kernel_object C S A0 B d0 K0) A0 A1 (@iso_evidence_to C A0 A1 iso) (@computational_kernel_morphism C S A0 B d0 K0)) (@computational_kernel_morphism C S A1 B d1 K1) (@kernel_domain_comparison_source_factor C S A0 A1 B d0 d1 K0 K1 iso comparison)
    : τ (@= (Hom C (@computational_kernel_object C S A1 B d1 K1) A1)
      (@comp_fapp0 C (@computational_kernel_object C S A1 B d1 K1) (@computational_kernel_object C S A0 B d0 K0) A1 (@comp_fapp0 C (@computational_kernel_object C S A0 B d0 K0) A0 A1 (@iso_evidence_to C A0 A1 iso) (@computational_kernel_morphism C S A0 B d0 K0)) (@hom_postcomp_factor_arrow C (@computational_kernel_object C S A0 B d0 K0) A1 (@computational_kernel_object C S A1 B d1 K1) (@comp_fapp0 C (@computational_kernel_object C S A0 B d0 K0) A0 A1 (@iso_evidence_to C A0 A1 iso) (@computational_kernel_morphism C S A0 B d0 K0)) (@computational_kernel_morphism C S A1 B d1 K1) (@kernel_domain_comparison_source_factor C S A0 A1 B d0 d1 K0 K1 iso comparison))) (@computational_kernel_morphism C S A1 B d1 K1));

assertnot
  (C : Cat) (S : τ (@PreadditiveCategory C)) (A0 A1 B : τ (Obj C))
  (d0 : τ (Hom C A0 B)) (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0
    (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  (other : τ (Hom C (@computational_kernel_object C S A1 B d1 K1) (@computational_kernel_object C S A0 B d0 K0)))
  ⊢ (@hom_postcomp_factor_arrow C (@computational_kernel_object C S A0 B d0 K0) A1 (@computational_kernel_object C S A1 B d1 K1) (@comp_fapp0 C (@computational_kernel_object C S A0 B d0 K0) A0 A1 (@iso_evidence_to C A0 A1 iso) (@computational_kernel_morphism C S A0 B d0 K0)) (@computational_kernel_morphism C S A1 B d1 K1) (@kernel_domain_comparison_source_factor C S A0 A1 B d0 d1 K0 K1 iso comparison)) ≡ other;
