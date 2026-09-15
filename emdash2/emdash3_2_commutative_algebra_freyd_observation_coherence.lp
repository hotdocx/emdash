/* Coherence of the concrete CAS-facing arrow interpretations.
   Objects are finite presentation data, hence a set; this does not make the
   directed Freyd category discrete or replace categorical universality. */
require open emdash.emdash3_2_commutative_algebra_freyd_arrow_observations;

// Finite presentation data is set-valued, using existing truncation owners.
symbol comm_ring_presentation_is_set (R : τ CommRing)
  : τ (IsSetGrpd (@CommRingPresentation R))
≔ @is_trunc_sigma trunc_zero Nat_grpd
    (λ generators : τ Nat_grpd,
      `Σ_ relations : τ Nat_grpd, @CommRingMatrix R generators relations)
    nat_is_set
    (λ generators : τ Nat_grpd,
      @is_trunc_sigma trunc_zero Nat_grpd
        (λ relations : τ Nat_grpd, @CommRingMatrix R generators relations)
        nat_is_set
        (λ relations : τ Nat_grpd,
          @finite_family_is_set (@CommRingVector R generators)
            (@finite_family_is_set (@comm_ring_carrier R)
              (@comm_ring_carrier_is_set R) generators) relations));

// Decoded endpoint views of the existing nested-Sigma arrow object.
// These are CAS-facing data observations, not new directed action owners.
symbol freyd_arrow_observation_source [R : τ CommRing]
  (u : τ (FreydArrowObservation R)) : τ (@CommRingPresentation R)
≔ sigma_Fst u;

symbol freyd_arrow_observation_target [R : τ CommRing]
  (u : τ (FreydArrowObservation R)) : τ (@CommRingPresentation R)
≔ sigma_Fst (sigma_Snd u);

// Project an existing complete-arrow agreement to its source presentation.
symbol freyd_arrow_observation_source_path [R : τ CommRing]
  [u v : τ (FreydArrowObservation R)] (p : τ (@= (FreydArrowObservation R) u v))
  : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_source R u) (@freyd_arrow_observation_source R v))
≔ @eq_ap (FreydArrowObservation R) (@CommRingPresentation R)
    (@freyd_arrow_observation_source R) u v p;

// The same observation at the target presentation.
symbol freyd_arrow_observation_target_path [R : τ CommRing]
  [u v : τ (FreydArrowObservation R)] (p : τ (@= (FreydArrowObservation R) u v))
  : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_target R u) (@freyd_arrow_observation_target R v))
≔ @eq_ap (FreydArrowObservation R) (@CommRingPresentation R)
    (@freyd_arrow_observation_target R) u v p;

// Two adjacent complete-arrow agreements induce the same path at their
// shared presentation. No additional coherence or exactness claim is input.
symbol freyd_arrow_observation_endpoint_coherence [R : τ CommRing]
  [A B D A1 B1 D1 : τ (@CommRingPresentation R)]
  [f : τ (@CommRingFreydHomSet R A B)] [g : τ (@CommRingFreydHomSet R B D)]
  [f1 : τ (@CommRingFreydHomSet R A1 B1)] [g1 : τ (@CommRingFreydHomSet R B1 D1)]
  (p : τ (@= (FreydArrowObservation R)
    (@lax_edge (@CommRingFreydPresentation_cat R) A B f)
    (@lax_edge (@CommRingFreydPresentation_cat R) A1 B1 f1)))
  (q : τ (@= (FreydArrowObservation R)
    (@lax_edge (@CommRingFreydPresentation_cat R) B D g)
    (@lax_edge (@CommRingFreydPresentation_cat R) B1 D1 g1)))
  : τ (@= (@= (@CommRingPresentation R) B B1)
    (@freyd_arrow_observation_target_path R _ _ p)
    (@freyd_arrow_observation_source_path R _ _ q))
≔ @is_contr_center _ ((@comm_ring_presentation_is_set R) B B1
    (@freyd_arrow_observation_target_path R _ _ p)
    (@freyd_arrow_observation_source_path R _ _ q));
