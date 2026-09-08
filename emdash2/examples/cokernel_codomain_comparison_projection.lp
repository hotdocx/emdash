/* The original forward cokernel map supplies the whole-iso projection law. */
require open emdash.emdash3_2_cokernel_codomain_comparison_projection;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A B0 B1 : τ (Obj C))
  (d0 : τ (Hom C A B0))
  (d1 : τ (Hom C A B1))
  (Q0 : τ (@ComputationalCokernel C S A B0 d0))
  (Q1 : τ (@ComputationalCokernel C S A B1 d1))
  (a : τ (@IsoEvidence C B0 B1))
  (comparison : τ (@= (Hom C A B1) d1
    (@comp_fapp0 C A B0 B1 (@iso_evidence_to C B0 B1 a) d0)))
  ⊢ @cokernel_codomain_comparison_to_path C S A B0 B1 d0 d1 Q0 Q1 a comparison : τ (@= (Hom C B0 (@computational_cokernel_object C S A B1 d1 Q1))
      (@comp_fapp0 C B0 (@computational_cokernel_object C S A B0 d0 Q0) (@computational_cokernel_object C S A B1 d1 Q1)
        (@iso_evidence_to C (@computational_cokernel_object C S A B0 d0 Q0) (@computational_cokernel_object C S A B1 d1 Q1) (@cokernel_codomain_comparison_iso C S A B0 B1 d0 d1 Q0 Q1 a comparison)) (@computational_cokernel_morphism C S A B0 d0 Q0))
      (@comp_fapp0 C B0 B1 (@computational_cokernel_object C S A B1 d1 Q1) (@computational_cokernel_morphism C S A B1 d1 Q1) (@iso_evidence_to C B0 B1 a)));
