/*
  An isomorphism of domains with d0 = d1 ∘ to induces an isomorphism of
  actual whole kernels. The two internal factor points are derived.
*/
require open emdash.emdash3_2_kernel_map_isos;

symbol kernel_domain_comparison_reverse_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 A1 B : τ (Obj C)]
  (d0 : τ (Hom C A0 B))
  (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0 (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  : τ (@= (Hom C A1 B) (@comp_fapp0 C A1 A0 B d0 (@iso_evidence_from C A0 A1 iso)) d1)
≔ (@eq_trans _ _ _ _
      (@eq_ap (Hom C A0 B) (Hom C A1 B)
        (λ h : τ (Hom C A0 B), @comp_fapp0 C A1 A0 B h (@iso_evidence_from C A0 A1 iso)) _ _ comparison)
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C A1 A0 A1 B d1 (@iso_evidence_to C A0 A1 iso) (@iso_evidence_from C A0 A1 iso)))
      (@eq_ap (Hom C A1 A1) (Hom C A1 B)
        (λ h : τ (Hom C A1 A1), @comp_fapp0 C A1 A1 B d1 h)
        _ _ (@iso_evidence_right C A0 A1 iso))));

symbol kernel_domain_comparison_forward_factor
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 A1 B : τ (Obj C)]
  (d0 : τ (Hom C A0 B))
  (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0 (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  : τ (@HomPrecompFactor C A0 B B d0 (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso)))
≔ @hom_precomp_factor_intro C A0 B B d0 (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))
    (@id C B) comparison;

symbol kernel_domain_comparison_reverse_factor
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 A1 B : τ (Obj C)]
  (d0 : τ (Hom C A0 B))
  (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0 (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  : τ (@HomPrecompFactor C A1 B B d1 (@comp_fapp0 C A1 A0 B d0 (@iso_evidence_from C A0 A1 iso)))
≔ @hom_precomp_factor_intro C A1 B B d1 (@comp_fapp0 C A1 A0 B d0 (@iso_evidence_from C A0 A1 iso))
    (@id C B) (@eq_sym _ _ _ (@kernel_domain_comparison_reverse_path C S A0 A1 B d0 d1 K0 K1 iso comparison));

symbol kernel_domain_comparison_iso
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A0 A1 B : τ (Obj C)]
  (d0 : τ (Hom C A0 B))
  (d1 : τ (Hom C A1 B))
  (K0 : τ (@ComputationalKernel C S A0 B d0))
  (K1 : τ (@ComputationalKernel C S A1 B d1))
  (iso : τ (@IsoEvidence C A0 A1))
  (comparison : τ (@= (Hom C A0 B) d0 (@comp_fapp0 C A0 A1 B d1 (@iso_evidence_to C A0 A1 iso))))
  : τ (@IsoEvidence C
      (@computational_kernel_object C S A0 B d0 K0)
      (@computational_kernel_object C S A1 B d1 K1))
≔ @computational_kernel_maps_iso C S A0 B A1 B d0 d1 K0 K1 (@iso_evidence_to C A0 A1 iso) (@iso_evidence_from C A0 A1 iso)
    (@kernel_domain_comparison_forward_factor C S A0 A1 B d0 d1 K0 K1 iso comparison)
    (@kernel_domain_comparison_reverse_factor C S A0 A1 B d0 d1 K0 K1 iso comparison)
    (@iso_evidence_left C A0 A1 iso)
    (@iso_evidence_right C A0 A1 iso);
