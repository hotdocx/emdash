/* Reviewer-facing quotient pairing and whole Freyd direct sums. */

require open emdash.emdash3_2_commutative_algebra_freyd_direct_sums;

assert (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R X P))
  (g : τ (@CommRingPresentationMorphism R X Q)) ⊢
  @comm_ring_freyd_pair R X P Q
    (@comm_ring_freyd_hom_class R X P f)
    (@comm_ring_freyd_hom_class R X Q g)
  ≡ @comm_ring_freyd_hom_class R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_pair R X P Q f g);

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @comm_ring_freyd_proj1_class R P Q
  : τ (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) P);

assert (R : τ CommRing) ⊢
  @comm_ring_freyd_direct_sum_func R
  : τ (@Functor
      (Product_cat
        (@CommRingFreydPresentation_cat R)
        (@CommRingFreydPresentation_cat R))
      (@CommRingFreydPresentation_cat R));

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @fapp0
    (Product_cat
      (@CommRingFreydPresentation_cat R)
      (@CommRingFreydPresentation_cat R))
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (Struct_sigma P Q)
  ≡ @comm_ring_presentation_direct_sum R P Q;

assert (R : τ CommRing)
  (P0 P1 Q0 Q1 : τ (@CommRingPresentation R)) ⊢
  @comm_ring_freyd_direct_sum_hom_func R P0 P1 Q0 Q1
  : τ (@Functor
      (Hom_cat
        (Product_cat
          (@CommRingFreydPresentation_cat R)
          (@CommRingFreydPresentation_cat R))
        (Struct_sigma P0 P1)
        (Struct_sigma Q0 Q1))
      (Hom_cat
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_presentation_direct_sum R P0 P1)
        (@comm_ring_presentation_direct_sum R Q0 Q1)));

assertnot (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f f' : τ (@CommRingFreydHomSet R X P))
  (g : τ (@CommRingFreydHomSet R X Q)) ⊢
  @comm_ring_freyd_pair R X P Q f g
  ≡ @comm_ring_freyd_pair R X P Q f' g;
