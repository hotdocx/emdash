/*
  An isomorphism of codomains with d1 = to ∘ d0 induces an isomorphism of
  actual whole cokernels. The two internal factor points are derived.
*/
require open emdash.emdash3_2_cokernel_map_isos;

symbol cokernel_codomain_comparison_reverse_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B0 B1 : τ (Obj C)]
  (d0 : τ (Hom C A B0))
  (d1 : τ (Hom C A B1))
  (Q0 : τ (@ComputationalCokernel C S A B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A B1 d1))
  (iso : τ (@IsoEvidence C B0 B1))
  (comparison : τ (@= (Hom C A B1) d1 (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 iso) d0)))
  : τ (@= (Hom C A B0) (@comp_fapp0 C A B1 B0 (@iso_evidence_from C B0 B1 iso) d1) d0)
≔ (@eq_trans _ _ _ _
      (@eq_ap (Hom C A B1) (Hom C A B0)
        (λ h : τ (Hom C A B1), @comp_fapp0 C A B1 B0 (@iso_evidence_from C B0 B1 iso) h) _ _ comparison)
      (@eq_trans _ _ _ _
      (@comp_assoc C A B0 B1 B0 (@iso_evidence_from C B0 B1 iso) (@iso_evidence_to C B0 B1 iso) d0)
      (@eq_ap (Hom C B0 B0) (Hom C A B0)
        (λ h : τ (Hom C B0 B0), @comp_fapp0 C A B0 B0 h d0)
        _ _ (@iso_evidence_left C B0 B1 iso))));

symbol cokernel_codomain_comparison_forward_factor
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B0 B1 : τ (Obj C)]
  (d0 : τ (Hom C A B0))
  (d1 : τ (Hom C A B1))
  (Q0 : τ (@ComputationalCokernel C S A B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A B1 d1))
  (iso : τ (@IsoEvidence C B0 B1))
  (comparison : τ (@= (Hom C A B1) d1 (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 iso) d0)))
  : τ (@HomPostcompFactor C A B1 A d1 (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 iso) d0))
≔ @hom_postcomp_factor_intro C A B1 A d1 (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 iso) d0)
    (@id C A) comparison;

symbol cokernel_codomain_comparison_reverse_factor
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B0 B1 : τ (Obj C)]
  (d0 : τ (Hom C A B0))
  (d1 : τ (Hom C A B1))
  (Q0 : τ (@ComputationalCokernel C S A B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A B1 d1))
  (iso : τ (@IsoEvidence C B0 B1))
  (comparison : τ (@= (Hom C A B1) d1 (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 iso) d0)))
  : τ (@HomPostcompFactor C A B0 A d0 (@comp_fapp0 C A B1 B0 (@iso_evidence_from C B0 B1 iso) d1))
≔ @hom_postcomp_factor_intro C A B0 A d0 (@comp_fapp0 C A B1 B0 (@iso_evidence_from C B0 B1 iso) d1)
    (@id C A) (@eq_sym _ _ _ (@cokernel_codomain_comparison_reverse_path C S A B0 B1 d0 d1 Q0 Q1 iso comparison));

symbol cokernel_codomain_comparison_iso
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B0 B1 : τ (Obj C)]
  (d0 : τ (Hom C A B0))
  (d1 : τ (Hom C A B1))
  (Q0 : τ (@ComputationalCokernel C S A B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A B1 d1))
  (iso : τ (@IsoEvidence C B0 B1))
  (comparison : τ (@= (Hom C A B1) d1 (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 iso) d0)))
  : τ (@IsoEvidence C
      (@computational_cokernel_object C S A B0 d0 Q0)
      (@computational_cokernel_object C S A B1 d1 Q1))
≔ @computational_cokernel_maps_iso C S A B0 A B1 d0 d1 Q0 Q1 (@iso_evidence_to C B0 B1 iso) (@iso_evidence_from C B0 B1 iso)
    (@cokernel_codomain_comparison_forward_factor C S A B0 B1 d0 d1 Q0 Q1 iso comparison)
    (@cokernel_codomain_comparison_reverse_factor C S A B0 B1 d0 d1 Q0 Q1 iso comparison)
    (@iso_evidence_left C B0 B1 iso)
    (@iso_evidence_right C B0 B1 iso);
