/* Reviewer-facing terminal zero presentation. */

require open emdash.emdash3_2_commutative_algebra_freyd_terminal_zero;

assert (R : τ CommRing) ⊢
  @comm_ring_freyd_terminal_zero R
  : τ (@TerminalObject
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R));

assert (R : τ CommRing)
  (P : τ (@CommRingPresentation R)) ⊢
  @terminal_hom_contr
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R) P
  ≡ @comm_ring_freyd_zero_terminal_hom_contr R P;

assert (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  (f : τ (@CommRingFreydHomSet R P
    (@comm_ring_zero_presentation R))) ⊢
  @comm_ring_freyd_to_zero_path R P f
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R))
      f
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R)));

assert (R : τ CommRing)
  (P : τ (@CommRingPresentation R)) ⊢
  @comm_ring_freyd_terminal_zero_arrow_path R P
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R))
      (@terminal_arrow_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R)
        (@comm_ring_freyd_terminal_zero R) P)
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R)));

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (h : τ (@CommRingFreydHomSet R P Q)) ⊢
  @comp_fapp0
    (@CommRingFreydPresentation_cat R)
    P Q (@comm_ring_zero_presentation R)
    (@terminal_arrow_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R)
      (@comm_ring_freyd_terminal_zero R) Q)
    h
  ≡ @terminal_arrow_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R)
      (@comm_ring_freyd_terminal_zero R) P;
