/* Reviewer-facing additive formal Freyd category. */

require open emdash.emdash3_2_commutative_algebra_freyd_additive;

assert (R : τ CommRing) ⊢
  @comm_ring_freyd_additive R
  : τ (@AdditiveCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R));

assert (R : τ CommRing)
  (P : τ (@CommRingPresentation R)) ⊢
  @additive_initial_hom_contr
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_additive R) P
  : τ (IsContr (@CommRingFreydHomSet R
      (@comm_ring_zero_presentation R) P));

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @additive_biproduct_identity_path
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_additive R) P Q
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_direct_sum R P Q))
      (@additive_biproduct_identity_sum
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_zero_presentation R)
        (@comm_ring_freyd_additive R) P Q)
      (@id (@CommRingFreydPresentation_cat R)
        (@comm_ring_presentation_direct_sum R P Q)));

assert (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (f : τ (@CommRingFreydHomSet R P S))
  (g : τ (@CommRingFreydHomSet R Q S)) ⊢
  @additive_copair_inj2_path
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_additive R) P Q S f g
  : τ (@= (@CommRingFreydHomSet R Q S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        Q (@comm_ring_presentation_direct_sum R P Q) S
        (@additive_copair_fapp0
          (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_direct_sum_func R)
          (@comm_ring_zero_presentation R)
          (@comm_ring_freyd_additive R) P Q S f g)
        (@additive_inj2_fapp0
          (@CommRingFreydPresentation_cat R)
          (@comm_ring_freyd_direct_sum_func R)
          (@comm_ring_zero_presentation R)
          (@comm_ring_freyd_additive R) P Q))
      g);
