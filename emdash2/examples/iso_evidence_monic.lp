/* Independent typed consumer at the original supplied choices. */
require open emdash.emdash3_2_iso_evidence_monic;

assert
  (C : Cat) (A B : τ (Obj C))
  (iso : τ (@IsoEvidence C A B))
  ⊢ @iso_evidence_to_is_monic C A B iso : τ (@IsMonic C A B (@iso_evidence_to C A B iso));
