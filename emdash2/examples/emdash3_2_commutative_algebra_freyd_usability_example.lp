/* Reviewer-facing generic Freyd category usability consumer. */

require open emdash.emdash3_2_commutative_algebra_freyd_usability;

symbol freyd_generic_identity_class_reviewer_path
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R P P)
      (@id (@CommRingFreydPresentation_cat R) P)
      (@comm_ring_freyd_identity_class R P))
≔ @comm_ring_freyd_identity_usability_path R P;

symbol freyd_generic_composition_reviewer_path
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@comm_ring_freyd_comp R P Q S g f))
≔ @comm_ring_freyd_comp_usability_path R P Q S g f;

assertnot
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  (h : τ (@CommRingFreydHomSet R P S))
  ⊢ @comm_ring_freyd_comp R P Q S g f
  ≡ h;
