/* Original arrow-observation carrier and raw introduction, independent of
   any homology model. These names and bodies are shared with the legacy view. */
require open emdash.emdash3_2_commutative_algebra_freyd_presentations;
require open emdash.emdash3_2_cubical_internalization;

// This is the EXISTING native arrow-object carrier, not a new diagram record.
symbol FreydArrowObservation (R : τ CommRing) : Grpd
≔ Obj (@LaxArrow_cat (@CommRingFreydPresentation_cat R));

symbol freyd_raw_arrow_observation [R : τ CommRing]
  [A B : τ (@CommRingPresentation R)] (f : τ (@CommRingPresentationMorphism R A B))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) A B (@comm_ring_freyd_hom_class R A B f);
