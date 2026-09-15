/* Existing Freyd Ω-arrow carrier, independent of the LES construction. */
require open emdash.emdash3_2_arrow_equivalence_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_arrow_observations;

// Sigma observation of an existing arrow and its existing fixed-arrow evidence.
symbol FreydOmegaArrowObservation (R : τ CommRing) : Grpd
≔ OmegaArrowData (@CommRingFreydPresentation_cat R);
symbol FreydArrowOmegaEvidence (R : τ CommRing) (a : τ (FreydArrowObservation R)) : Grpd
≔ @ArrowOmegaEvidence (@CommRingFreydPresentation_cat R) a;
symbol freyd_omega_arrow_observation [R : τ CommRing] (d : τ (FreydOmegaArrowObservation R))
  : τ (FreydArrowObservation R)
≔ @omega_arrow_observation (@CommRingFreydPresentation_cat R) d;
symbol freyd_omega_arrow_evidence [R : τ CommRing] (d : τ (FreydOmegaArrowObservation R))
  : τ (FreydArrowOmegaEvidence R (@freyd_omega_arrow_observation R d))
≔ @omega_arrow_observation_evidence (@CommRingFreydPresentation_cat R) d;
