/* Finite native arrow-diagram observations. This is result data derived
   from the existing finite arrow tails, not another category of complexes. */
require open emdash.emdash3_2_commutative_algebra_freyd_observation_coherence;
require open emdash.emdash3_2_finite_family_paths;
require open emdash.emdash3_2_finite_arrow_tail_arrows;

// Each additional arrow must start at the preceding arrow's target.
symbol FreydArrowMatchingTail [R : τ CommRing]
  (a : τ (FreydArrowObservation R)) (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (FreydArrowObservation R) n)) : Grpd
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (FreydArrowObservation R)
      (λ _ : τ (FreydArrowObservation R),
        @Function_grpd (@FiniteFamily (FreydArrowObservation R) n0) Grpd_grpd))
    (λ _ : τ (FreydArrowObservation R),
      λ _ : τ (@FiniteFamily (FreydArrowObservation R) zero), Unit_grpd)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ a0 : τ (FreydArrowObservation R),
      λ ys : τ (@FiniteFamily (FreydArrowObservation R) (succ n0)),
        @Σ_ (@= (@CommRingPresentation R) (@freyd_arrow_observation_target R a0)
          (@freyd_arrow_observation_source R (@finite_family_head _ n0 ys)))
          (λ _ : τ _, rec (@finite_family_head _ n0 ys) (@finite_family_tail _ n0 ys)))
    n) a xs;

symbol freyd_arrow_matching_nil [R : τ CommRing] (a : τ (FreydArrowObservation R))
  : τ (@FreydArrowMatchingTail R a zero (@finite_family_nil (FreydArrowObservation R)))
≔ tt;

symbol freyd_arrow_matching_cons [R : τ CommRing] [n : τ Nat_grpd]
  [a b : τ (FreydArrowObservation R)] [xs : τ (@FiniteFamily (FreydArrowObservation R) n)]
  (e : τ (@= (@CommRingPresentation R)
    (@freyd_arrow_observation_target R a) (@freyd_arrow_observation_source R b)))
  (rest : τ (@FreydArrowMatchingTail R b n xs))
  : τ (@FreydArrowMatchingTail R a (succ n) (@finite_family_cons _ n b xs))
≔ Struct_sigma e rest;

// Matching is a proposition because presentation endpoints form a set.
symbol freyd_arrow_matching_is_prop [R : τ CommRing]
  (a : τ (FreydArrowObservation R)) (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily (FreydArrowObservation R) n))
  : τ (IsPropGrpd (@FreydArrowMatchingTail R a n xs))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (FreydArrowObservation R)
      (λ a0 : τ (FreydArrowObservation R),
        @Pi_grpd (@FiniteFamily (FreydArrowObservation R) n0)
          (λ ys : τ (@FiniteFamily (FreydArrowObservation R) n0),
            IsPropGrpd (@FreydArrowMatchingTail R a0 n0 ys))))
    (λ _ : τ (FreydArrowObservation R),
      λ _ : τ (@FiniteFamily (FreydArrowObservation R) zero), unit_is_prop)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ a0 : τ (FreydArrowObservation R),
      λ ys : τ (@FiniteFamily (FreydArrowObservation R) (succ n0)),
        @is_trunc_sigma trunc_minus_one
          (@= (@CommRingPresentation R) (@freyd_arrow_observation_target R a0)
            (@freyd_arrow_observation_source R (@finite_family_head _ n0 ys)))
          (λ _ : τ _, @FreydArrowMatchingTail R (@finite_family_head _ n0 ys)
            n0 (@finite_family_tail _ n0 ys))
          ((@comm_ring_presentation_is_set R) (@freyd_arrow_observation_target R a0)
            (@freyd_arrow_observation_source R (@finite_family_head _ n0 ys)))
          (λ _ : τ _, rec (@finite_family_head _ n0 ys) (@finite_family_tail _ n0 ys)))
    n) a xs;

// Nonempty complete-arrow observations with their endpoint matching property.
symbol FreydArrowObservationDiagram (R : τ CommRing) (n : τ Nat_grpd) : Grpd
≔ @Σ_ (@FiniteFamily (FreydArrowObservation R) (succ n))
    (λ xs : τ (@FiniteFamily (FreydArrowObservation R) (succ n)),
      @FreydArrowMatchingTail R (@finite_family_head _ n xs) n (@finite_family_tail _ n xs));

symbol freyd_arrow_diagram_intro [R : τ CommRing] [n : τ Nat_grpd]
  (a : τ (FreydArrowObservation R)) (xs : τ (@FiniteFamily (FreydArrowObservation R) n))
  (matching : τ (@FreydArrowMatchingTail R a n xs))
  : τ (FreydArrowObservationDiagram R n)
≔ Struct_sigma (@finite_family_cons _ n a xs) matching;

symbol freyd_arrow_diagram_arrows [R : τ CommRing] [n : τ Nat_grpd]
  (d : τ (FreydArrowObservationDiagram R n))
  : τ (@FiniteFamily (FreydArrowObservation R) (succ n))
≔ sigma_Fst d;

// The whole observation path is determined by its existing arrow paths.
// Fibre compatibility is derived from proposition-valued matching.
symbol freyd_arrow_diagram_path [R : τ CommRing] [n : τ Nat_grpd]
  [a b : τ (FreydArrowObservation R)]
  [xs ys : τ (@FiniteFamily (FreydArrowObservation R) n)]
  (mx : τ (@FreydArrowMatchingTail R a n xs))
  (my : τ (@FreydArrowMatchingTail R b n ys))
  (p : τ (@= (FreydArrowObservation R) a b))
  (q : τ (@= (@FiniteFamily (FreydArrowObservation R) n) xs ys))
  : τ (@= (FreydArrowObservationDiagram R n)
    (@freyd_arrow_diagram_intro R n a xs mx) (@freyd_arrow_diagram_intro R n b ys my))
≔ @sigma_path_intro (@FiniteFamily (FreydArrowObservation R) (succ n))
    (λ zs : τ (@FiniteFamily (FreydArrowObservation R) (succ n)),
      @FreydArrowMatchingTail R (@finite_family_head _ n zs) n (@finite_family_tail _ n zs))
    (@finite_family_cons _ n a xs) (@finite_family_cons _ n b ys) mx my
    (@finite_family_cons_path _ n a b xs ys p q)
    (@is_contr_center _ ((@freyd_arrow_matching_is_prop R a n xs) mx
      (@ind_eq _ _ _ (@finite_family_cons_path _ n a b xs ys p q)
        (λ zs : τ (@FiniteFamily (FreydArrowObservation R) (succ n)),
          @FreydArrowMatchingTail R (@finite_family_head _ n zs) n (@finite_family_tail _ n zs)) my)));

// Matching introduction for an arbitrary visible successor tuple.
symbol freyd_arrow_matching_step [R : τ CommRing] [n : τ Nat_grpd]
  (a : τ (FreydArrowObservation R))
  (ys : τ (@FiniteFamily (FreydArrowObservation R) (succ n)))
  (e : τ (@= (@CommRingPresentation R) (@freyd_arrow_observation_target R a)
    (@freyd_arrow_observation_source R (@finite_family_head _ n ys))))
  (rest : τ (@FreydArrowMatchingTail R (@finite_family_head _ n ys) n (@finite_family_tail _ n ys)))
  : τ (@FreydArrowMatchingTail R a (succ n) ys)
≔ Struct_sigma e rest;

// The original finite-tail arrow observer retains its given first arrow.
symbol freyd_arrow_tail_first_path [R : τ CommRing] (Q : Π A : τ (@CommRingPresentation R), Π B : τ
  (@CommRingPresentation R),
    Π D : τ (@CommRingPresentation R),
    τ (@CommRingFreydHomSet R A B) → τ (@CommRingFreydHomSet R B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (@CommRingPresentation R)]
  [f : τ (@CommRingFreydHomSet R A B)] (xs : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q n A B f))
  : τ (@= (FreydArrowObservation R) (@finite_family_head (FreydArrowObservation R) n (@finite_arrow_tail_arrows
    (@CommRingFreydPresentation_cat R) Q n A B f xs)) (@lax_edge (@CommRingFreydPresentation_cat R) A B f))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (@CommRingPresentation R)
      (λ A0 : τ (@CommRingPresentation R), @Pi_grpd (@CommRingPresentation R)
        (λ B0 : τ (@CommRingPresentation R), @Pi_grpd (@CommRingFreydHomSet R A0 B0)
          (λ f0 : τ (@CommRingFreydHomSet R A0 B0), @Pi_grpd (@FiniteArrowTail (@CommRingFreydPresentation_cat
            R) Q n0 A0 B0 f0)
            (λ xs0 : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0), (@=
              (FreydArrowObservation R) (@finite_family_head (FreydArrowObservation R) n0
              (@finite_arrow_tail_arrows (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0)) (@lax_edge
              (@CommRingFreydPresentation_cat R) A0 B0 f0)))))))
    (λ A0 : τ (@CommRingPresentation R), λ B0 : τ (@CommRingPresentation R),
      λ f0 : τ (@CommRingFreydHomSet R A0 B0), λ xs0 : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q
        zero A0 B0 f0), @eq_refl (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R) A0 B0
        f0))
    (λ n0 : τ Nat_grpd, λ _ : τ _, λ A0 : τ (@CommRingPresentation R), λ B0 : τ (@CommRingPresentation R),
      λ f0 : τ (@CommRingFreydHomSet R A0 B0), λ xs0 : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q
        (succ n0) A0 B0 f0), @eq_refl (FreydArrowObservation R) (@lax_edge (@CommRingFreydPresentation_cat R) A0
        B0 f0))
    n) A B f xs;

// Every existing indexed tail has matching complete-arrow observations.
symbol freyd_arrow_tail_matching [R : τ CommRing] (Q : Π A : τ (@CommRingPresentation R), Π B : τ
  (@CommRingPresentation R),
    Π D : τ (@CommRingPresentation R),
    τ (@CommRingFreydHomSet R A B) → τ (@CommRingFreydHomSet R B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (@CommRingPresentation R)]
  [f : τ (@CommRingFreydHomSet R A B)] (xs : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q n A B f))
  : τ (@FreydArrowMatchingTail R (@lax_edge (@CommRingFreydPresentation_cat R) A B f) n (@finite_family_tail
    (FreydArrowObservation R) n (@finite_arrow_tail_arrows (@CommRingFreydPresentation_cat R) Q n A B f xs)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (@CommRingPresentation R)
      (λ A0 : τ (@CommRingPresentation R), @Pi_grpd (@CommRingPresentation R)
        (λ B0 : τ (@CommRingPresentation R), @Pi_grpd (@CommRingFreydHomSet R A0 B0)
          (λ f0 : τ (@CommRingFreydHomSet R A0 B0), @Pi_grpd (@FiniteArrowTail (@CommRingFreydPresentation_cat
            R) Q n0 A0 B0 f0)
            (λ xs0 : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0),
              (@FreydArrowMatchingTail R (@lax_edge (@CommRingFreydPresentation_cat R) A0 B0 f0) n0
              (@finite_family_tail (FreydArrowObservation R) n0 (@finite_arrow_tail_arrows
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0))))))))
    (λ A0 : τ (@CommRingPresentation R), λ B0 : τ (@CommRingPresentation R),
      λ f0 : τ (@CommRingFreydHomSet R A0 B0), λ xs0 : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q
        zero A0 B0 f0), tt)
    (λ n0 : τ Nat_grpd, λ rec : τ _, λ A0 : τ (@CommRingPresentation R), λ B0 : τ (@CommRingPresentation R),
      λ f0 : τ (@CommRingFreydHomSet R A0 B0), λ xs0 : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q
        (succ n0) A0 B0 f0),
      @freyd_arrow_matching_step R n0 (@lax_edge (@CommRingFreydPresentation_cat R) A0 B0 f0)
        (@finite_arrow_tail_arrows (@CommRingFreydPresentation_cat R) Q n0 B0 (@finite_arrow_tail_next
        (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow
        (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_rest
        (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0))
        (@eq_sym _ _ _ (@eq_ap (FreydArrowObservation R) (@CommRingPresentation R)
          (@freyd_arrow_observation_source R) _ _ (@freyd_arrow_tail_first_path R Q n0 B0
            (@finite_arrow_tail_next (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0)
            (@finite_arrow_tail_arrow (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0)
            (@finite_arrow_tail_rest (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0))))
        (@ind_eq _ _ _ (@freyd_arrow_tail_first_path R Q n0 B0 (@finite_arrow_tail_next
          (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow
          (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_rest
          (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0))
          (λ a0 : τ (FreydArrowObservation R), @FreydArrowMatchingTail R a0 n0
            (@finite_family_tail (FreydArrowObservation R) n0 (@finite_arrow_tail_arrows
              (@CommRingFreydPresentation_cat R) Q n0 B0 (@finite_arrow_tail_next
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_rest
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0)))) (rec B0 (@finite_arrow_tail_next
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_rest
              (@CommRingFreydPresentation_cat R) Q n0 A0 B0 f0 xs0))))
    n) A B f xs;

// A derived observation of the EXISTING finite tail; no tail eta is assumed.
symbol freyd_arrow_tail_diagram [R : τ CommRing] (Q : Π A : τ (@CommRingPresentation R), Π B : τ
  (@CommRingPresentation R),
    Π D : τ (@CommRingPresentation R),
    τ (@CommRingFreydHomSet R A B) → τ (@CommRingFreydHomSet R B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (@CommRingPresentation R)]
  [f : τ (@CommRingFreydHomSet R A B)] (xs : τ (@FiniteArrowTail (@CommRingFreydPresentation_cat R) Q n A B f))
  : τ (FreydArrowObservationDiagram R n)
≔ Struct_sigma (@finite_arrow_tail_arrows (@CommRingFreydPresentation_cat R) Q n A B f xs)
    (@ind_eq _ _ _ (@freyd_arrow_tail_first_path R Q n A B f xs)
      (λ a : τ (FreydArrowObservation R), @FreydArrowMatchingTail R a n
        (@finite_family_tail (FreydArrowObservation R) n (@finite_arrow_tail_arrows
          (@CommRingFreydPresentation_cat R) Q n A B f xs))) (@freyd_arrow_tail_matching R Q n A B f xs));

// Transport only the proposition-valued endpoint matching along the arrow paths.
symbol freyd_arrow_matching_transport [R : τ CommRing] [n : τ Nat_grpd]
  [a b : τ (FreydArrowObservation R)]
  [xs ys : τ (@FiniteFamily (FreydArrowObservation R) n)]
  (m : τ (@FreydArrowMatchingTail R a n xs))
  (p : τ (@= (FreydArrowObservation R) a b))
  (q : τ (@= (@FiniteFamily (FreydArrowObservation R) n) xs ys))
  : τ (@FreydArrowMatchingTail R b n ys)
≔ @ind_eq (FreydArrowObservation R) b a (@eq_sym _ _ _ p)
    (λ u : τ (FreydArrowObservation R), @FreydArrowMatchingTail R u n ys)
    (@ind_eq (@FiniteFamily (FreydArrowObservation R) n) ys xs (@eq_sym _ _ _ q)
      (λ zs : τ (@FiniteFamily (FreydArrowObservation R) n), @FreydArrowMatchingTail R a n zs) m);
