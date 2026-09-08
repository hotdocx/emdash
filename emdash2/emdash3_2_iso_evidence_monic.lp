/* Monicity comes from the existing inverse, not from a new assumption. */
require open emdash.emdash3_2_mono_epi_comparisons;

symbol iso_evidence_to_is_monic
  [C : Cat] [A B : τ (Obj C)]
  (iso : τ (@IsoEvidence C A B))
  : τ (@IsMonic C A B (@iso_evidence_to C A B iso))
≔ @is_monic_of_monic_factor C A B A
    (@iso_evidence_to C A B iso) (@iso_evidence_from C A B iso)
    (@id C A) (@iso_evidence_left C A B iso)
    (λ T : τ (Obj C), λ u : τ (Hom C T A), λ v : τ (Hom C T A),
      λ path : τ (@= (Hom C T A) u v), path);
