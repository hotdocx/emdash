/*
  Recursive bounded complexes in the formal Freyd category.

  Terms are presentations, differentials are raw presentation morphisms, and
  each successor stores the existing adjacent-zero agreement. The first
  interior degree delegates directly to witnessed one-degree homology. This
  is an iterator over that owner, not a second homology theory. No rule or
  unification equation is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_functorial_homology;

symbol CommRingFreydChainTail
  (R : τ CommRing)
  (length : τ Nat_grpd)
  (below current : τ (@CommRingPresentation R))
  (boundary : τ (@CommRingPresentationMorphism R current below))
  : Grpd
≔ (@nat_elim
    (λ length0 : τ Nat_grpd,
      @Pi_grpd (@CommRingPresentation R) (λ below0 : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ current0 : τ _,
          @Function_grpd
            (@CommRingPresentationMorphism R current0 below0)
            Grpd_grpd)))
    (λ _ : τ (@CommRingPresentation R),
      λ _ : τ (@CommRingPresentation R),
      λ _ : τ _, Unit_grpd)
    (λ length0 : τ Nat_grpd,
      λ rec : τ _,
      λ below0 : τ (@CommRingPresentation R),
      λ current0 : τ (@CommRingPresentation R),
      λ boundary0 : τ (@CommRingPresentationMorphism R current0 below0),
        `Σ_ next : τ (@CommRingPresentation R),
          `Σ_ differential : τ (@CommRingPresentationMorphism R next current0),
            @Product_grpd
              (@CommRingFreydChainPair R next current0 below0
                differential boundary0)
              (rec current0 next differential))
    length) below current boundary;

symbol comm_ring_freyd_chain_tail_nil
  [R : τ CommRing]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  : τ (@CommRingFreydChainTail R zero below current boundary)
≔ tt;

symbol comm_ring_freyd_chain_tail_cons
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  (next : τ (@CommRingPresentation R))
  (differential : τ (@CommRingPresentationMorphism R next current))
  (law : τ (@CommRingFreydChainPair R next current below
    differential boundary))
  (rest : τ (@CommRingFreydChainTail R length current next differential))
  : τ (@CommRingFreydChainTail R (succ length) below current boundary)
≔ @Struct_sigma
    (@CommRingPresentation R)
    (λ next0 : τ _,
      `Σ_ differential0 : τ (@CommRingPresentationMorphism R next0 current),
        @Product_grpd
          (@CommRingFreydChainPair R next0 current below
            differential0 boundary)
          (@CommRingFreydChainTail R length current next0 differential0))
    next
    (@Struct_sigma
      (@CommRingPresentationMorphism R next current)
      (λ differential0 : τ _,
        @Product_grpd
          (@CommRingFreydChainPair R next current below differential0 boundary)
          (@CommRingFreydChainTail R length current next differential0))
      differential
      (@Product_pair_grpd _ _ law rest));

symbol comm_ring_freyd_chain_tail_next
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  (tail : τ (@CommRingFreydChainTail R
    (succ length) below current boundary))
  : τ (@CommRingPresentation R)
≔ sigma_Fst tail;

symbol comm_ring_freyd_chain_tail_differential
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  (tail : τ (@CommRingFreydChainTail R
    (succ length) below current boundary))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_chain_tail_next R length below current boundary tail)
      current)
≔ sigma_Fst (sigma_Snd tail);

symbol comm_ring_freyd_chain_tail_law
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  (tail : τ (@CommRingFreydChainTail R
    (succ length) below current boundary))
  : τ (@CommRingFreydChainPair R
      (@comm_ring_freyd_chain_tail_next R length below current boundary tail)
      current below
      (@comm_ring_freyd_chain_tail_differential R
        length below current boundary tail)
      boundary)
≔ sigma_Fst (sigma_Snd (sigma_Snd tail));

symbol comm_ring_freyd_chain_tail_rest
  [R : τ CommRing]
  [length : τ Nat_grpd]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  (tail : τ (@CommRingFreydChainTail R
    (succ length) below current boundary))
  : τ (@CommRingFreydChainTail R length current
      (@comm_ring_freyd_chain_tail_next R length below current boundary tail)
      (@comm_ring_freyd_chain_tail_differential R
        length below current boundary tail))
≔ sigma_Snd (sigma_Snd (sigma_Snd tail));

symbol CommRingFreydBoundedComplex
  (R : τ CommRing)
  (length : τ Nat_grpd)
  : Grpd
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Grpd_cat)
    (@CommRingPresentation R)
    (λ tailLength : τ Nat_grpd,
      λ _ : Grpd,
        `Σ_ P0 : τ (@CommRingPresentation R),
          `Σ_ P1 : τ (@CommRingPresentation R),
            `Σ_ d1 : τ (@CommRingPresentationMorphism R P1 P0),
              @CommRingFreydChainTail R tailLength P0 P1 d1)
    length;

symbol comm_ring_freyd_bounded_complex_zero
  [R : τ CommRing]
  (P0 : τ (@CommRingPresentation R))
  : τ (@CommRingFreydBoundedComplex R zero)
≔ P0;

symbol comm_ring_freyd_bounded_complex_succ
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (P0 P1 : τ (@CommRingPresentation R))
  (d1 : τ (@CommRingPresentationMorphism R P1 P0))
  (tail : τ (@CommRingFreydChainTail R tailLength P0 P1 d1))
  : τ (@CommRingFreydBoundedComplex R (succ tailLength))
≔ @Struct_sigma
    (@CommRingPresentation R)
    (λ P00 : τ _,
      `Σ_ P10 : τ (@CommRingPresentation R),
        `Σ_ d10 : τ (@CommRingPresentationMorphism R P10 P00),
          @CommRingFreydChainTail R tailLength P00 P10 d10)
    P0
    (@Struct_sigma
      (@CommRingPresentation R)
      (λ P10 : τ _,
        `Σ_ d10 : τ (@CommRingPresentationMorphism R P10 P0),
          @CommRingFreydChainTail R tailLength P0 P10 d10)
      P1
      (@Struct_sigma
        (@CommRingPresentationMorphism R P1 P0)
        (λ d10 : τ _, @CommRingFreydChainTail R tailLength P0 P1 d10)
        d1 tail));

symbol comm_ring_freyd_bounded_complex_P0
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingFreydBoundedComplex R (succ tailLength)))
  : τ (@CommRingPresentation R)
≔ sigma_Fst C;

symbol comm_ring_freyd_bounded_complex_P1
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingFreydBoundedComplex R (succ tailLength)))
  : τ (@CommRingPresentation R)
≔ sigma_Fst (sigma_Snd C);

symbol comm_ring_freyd_bounded_complex_d1
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingFreydBoundedComplex R (succ tailLength)))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_bounded_complex_P1 R tailLength C)
      (@comm_ring_freyd_bounded_complex_P0 R tailLength C))
≔ sigma_Fst (sigma_Snd (sigma_Snd C));

symbol comm_ring_freyd_bounded_complex_tail
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingFreydBoundedComplex R (succ tailLength)))
  : τ (@CommRingFreydChainTail R tailLength
      (@comm_ring_freyd_bounded_complex_P0 R tailLength C)
      (@comm_ring_freyd_bounded_complex_P1 R tailLength C)
      (@comm_ring_freyd_bounded_complex_d1 R tailLength C))
≔ sigma_Snd (sigma_Snd (sigma_Snd C));

// Homology at the first interior degree of a nontrivial tail.
symbol comm_ring_freyd_chain_tail_first_homology
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [length : τ Nat_grpd]
  [below current : τ (@CommRingPresentation R)]
  [boundary : τ (@CommRingPresentationMorphism R current below)]
  (tail : τ (@CommRingFreydChainTail R
    (succ length) below current boundary))
  : τ (@CommRingFreydWitnessedHomologyAt R W
      (@comm_ring_freyd_chain_tail_next R length below current boundary tail)
      current below
      (@comm_ring_freyd_chain_tail_differential R
        length below current boundary tail)
      boundary
      (@comm_ring_freyd_chain_tail_law R length below current boundary tail))
≔ @comm_ring_freyd_witnessed_homology_at R W
    (@comm_ring_freyd_chain_tail_next R length below current boundary tail)
    current below
    (@comm_ring_freyd_chain_tail_differential R
      length below current boundary tail)
    boundary
    (@comm_ring_freyd_chain_tail_law R length below current boundary tail);
