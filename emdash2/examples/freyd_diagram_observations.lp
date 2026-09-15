/* Whole finite observation paths and retention of original indexed tails. */
require open emdash.emdash3_2_commutative_algebra_freyd_diagram_observations;

assert [A : Grpd] [n : τ Nat_grpd] (x : τ A) (xs : τ (@FiniteFamily A n)) ⊢
  @finite_family_cons_path A n x x xs xs (@eq_refl A x) (@eq_refl (@FiniteFamily A n) xs)
  ≡ @eq_refl (@FiniteFamily A (succ n)) (@finite_family_cons A n x xs);

assert [R : τ CommRing] (a : τ (FreydArrowObservation R)) ⊢
  @freyd_arrow_matching_nil R a
  : τ (@FreydArrowMatchingTail R a zero (@finite_family_nil (FreydArrowObservation R)));
assert [R : τ CommRing] (a : τ (FreydArrowObservation R)) (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (FreydArrowObservation R) n)) ⊢
  @freyd_arrow_matching_is_prop R a n xs : τ (IsPropGrpd (@FreydArrowMatchingTail R a n xs));
assert [R : τ CommRing] [n : τ Nat_grpd] (a b : τ (FreydArrowObservation R))
  (xs : τ (@FiniteFamily (FreydArrowObservation R) n))
  (e : τ (@= (@CommRingPresentation R) (@freyd_arrow_observation_target R a) (@freyd_arrow_observation_source R b)))
  (m : τ (@FreydArrowMatchingTail R b n xs)) ⊢
  sigma_Fst (@freyd_arrow_matching_cons R n a b xs e m) ≡ e;
assert [R : τ CommRing] [n : τ Nat_grpd] (a b : τ (FreydArrowObservation R))
  (xs : τ (@FiniteFamily (FreydArrowObservation R) n))
  (e : τ (@= (@CommRingPresentation R) (@freyd_arrow_observation_target R a) (@freyd_arrow_observation_source R b)))
  (m : τ (@FreydArrowMatchingTail R b n xs)) ⊢
  sigma_Snd (@freyd_arrow_matching_cons R n a b xs e m) ≡ m;
assert [R : τ CommRing] [n : τ Nat_grpd] (a : τ (FreydArrowObservation R))
  (xs : τ (@FiniteFamily (FreydArrowObservation R) n))
  (m : τ (@FreydArrowMatchingTail R a n xs)) ⊢
  @freyd_arrow_diagram_arrows R n (@freyd_arrow_diagram_intro R n a xs m)
  ≡ @finite_family_cons (FreydArrowObservation R) n a xs;
assert [R : τ CommRing] [n : τ Nat_grpd] (a b : τ (FreydArrowObservation R))
  (xs ys : τ (@FiniteFamily (FreydArrowObservation R) n))
  (mx : τ (@FreydArrowMatchingTail R a n xs)) (my : τ (@FreydArrowMatchingTail R b n ys))
  (p : τ (@= (FreydArrowObservation R) a b)) (q : τ (@= (@FiniteFamily (FreydArrowObservation R) n) xs ys)) ⊢
  @freyd_arrow_diagram_path R n a b xs ys mx my p q
  : τ (@= (FreydArrowObservationDiagram R n)
    (@freyd_arrow_diagram_intro R n a xs mx) (@freyd_arrow_diagram_intro R n b ys my));

symbol R : τ CommRing;
symbol Q : Π A : τ (@CommRingPresentation R), Π B : τ (@CommRingPresentation R),
  Π D : τ (@CommRingPresentation R), τ (@CommRingFreydHomSet R A B) → τ (@CommRingFreydHomSet R B D) → Grpd;
symbol n : τ Nat_grpd;
symbol A : τ (@CommRingPresentation R);
symbol B : τ (@CommRingPresentation R);
symbol D : τ (@CommRingPresentation R);
symbol f : τ (@CommRingFreydHomSet R A B);
symbol g : τ (@CommRingFreydHomSet R B D);
symbol q : τ (Q A B D f g);
symbol xs : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q n A B f);

// The new view retains the exact old observer even for an arbitrary tail.
assert ⊢ @freyd_arrow_diagram_arrows R n (@freyd_arrow_tail_diagram R Q n A B f xs)
  ≡ @finite_arrow_tail_arrows (@CommRingFreydPresentation_cat R) Q n A B f xs;
assert ⊢ @freyd_arrow_tail_first_path R Q n A B f xs
  : τ (@= (FreydArrowObservation R)
    (@finite_family_head (FreydArrowObservation R) n (@finite_arrow_tail_arrows (@CommRingFreydPresentation_cat R) Q n A B f xs))
    (@lax_edge (@CommRingFreydPresentation_cat R) A B f));
// Visible nonidentity arrows and the original constructor indices compute.
assert ⊢ @freyd_arrow_diagram_arrows R (succ zero)
  (@freyd_arrow_tail_diagram R Q (succ zero) A B f
    (@finite_arrow_tail_cons (@CommRingFreydPresentation_cat R) Q zero A B f D g q
      (@finite_arrow_tail_nil (@CommRingFreydPresentation_cat R) Q B D g)))
  ≡ @finite_family_cons (FreydArrowObservation R) (succ zero) (@lax_edge (@CommRingFreydPresentation_cat R) A B f)
    (@finite_family_cons (FreydArrowObservation R) zero (@lax_edge (@CommRingFreydPresentation_cat R) B D g)
      (@finite_family_nil (FreydArrowObservation R)));
