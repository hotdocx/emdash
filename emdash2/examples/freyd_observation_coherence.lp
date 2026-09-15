/* Concrete presentation endpoint coherence from existing arrow agreements. */
require open emdash.emdash3_2_commutative_algebra_freyd_observation_coherence;
// Arbitrary arrows and agreements; no identity-arrow specialization is assumed.
symbol R : τ CommRing;
symbol A : τ (@CommRingPresentation R);
symbol B : τ (@CommRingPresentation R);
symbol D : τ (@CommRingPresentation R);
symbol A1 : τ (@CommRingPresentation R);
symbol B1 : τ (@CommRingPresentation R);
symbol D1 : τ (@CommRingPresentation R);
symbol f : τ (@CommRingFreydHomSet R A B);
symbol g : τ (@CommRingFreydHomSet R B D);
symbol f1 : τ (@CommRingFreydHomSet R A1 B1);
symbol g1 : τ (@CommRingFreydHomSet R B1 D1);
symbol p : τ (@= (FreydArrowObservation R)
  (@lax_edge (@CommRingFreydPresentation_cat R) A B f)
  (@lax_edge (@CommRingFreydPresentation_cat R) A1 B1 f1));
symbol q : τ (@= (FreydArrowObservation R)
  (@lax_edge (@CommRingFreydPresentation_cat R) B D g)
  (@lax_edge (@CommRingFreydPresentation_cat R) B1 D1 g1));

assert ⊢ @comm_ring_presentation_is_set R : τ (IsSetGrpd (@CommRingPresentation R));
assert ⊢ @freyd_arrow_observation_source R (@lax_edge (@CommRingFreydPresentation_cat R) A B f) ≡ A;
assert ⊢ @freyd_arrow_observation_target R (@lax_edge (@CommRingFreydPresentation_cat R) A B f) ≡ B;
assert ⊢ @freyd_arrow_observation_source_path R _ _ p : τ (@= (@CommRingPresentation R) A A1);
assert ⊢ @freyd_arrow_observation_target_path R _ _ p : τ (@= (@CommRingPresentation R) B B1);
assert ⊢ @freyd_arrow_observation_endpoint_coherence R A B D A1 B1 D1 f g f1 g1 p q
  : τ (@= (@= (@CommRingPresentation R) B B1)
    (@freyd_arrow_observation_target_path R _ _ p)
    (@freyd_arrow_observation_source_path R _ _ q));
assert ⊢ @freyd_arrow_observation_source_path R _ _
  (@eq_refl (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R) A B f))
  ≡ @eq_refl (@CommRingPresentation R) A;
assert ⊢ @freyd_arrow_observation_target_path R _ _
  (@eq_refl (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R) A B f))
  ≡ @eq_refl (@CommRingPresentation R) B;

// An unrelated source cannot be silently used as the next shared endpoint.
assertnot ⊢ @freyd_arrow_observation_endpoint_coherence R A B D A1 B1 D1 f g f1 g1 p p
  : τ (@= (@= (@CommRingPresentation R) B B1)
    (@freyd_arrow_observation_target_path R _ _ p)
    (@freyd_arrow_observation_source_path R _ _ q));
