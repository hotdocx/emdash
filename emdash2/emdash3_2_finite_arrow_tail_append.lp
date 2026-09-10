/* Final-edge observations and append, sharing that actual boundary arrow. */
require open emdash.emdash3_2_finite_arrow_tails;

symbol finite_arrow_tail_last_source
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q n A B f)) : τ (Obj C)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
        @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
          @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
            @Pi_grpd (@FiniteArrowTail C Q n0 A0 B0 f0) (λ xs0 : τ _, (Obj C))))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ _ : τ (@FiniteArrowTail C Q zero A0 B0 f0), A0)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ n0) A0 B0 f0),
        rec B0 (@finite_arrow_tail_next C Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow C Q n0 A0 B0 f0 xs0)
          (@finite_arrow_tail_rest C Q n0 A0 B0 f0 xs0))
    n) A B f xs;

symbol finite_arrow_tail_last_target
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q n A B f)) : τ (Obj C)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
        @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
          @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
            @Pi_grpd (@FiniteArrowTail C Q n0 A0 B0 f0) (λ xs0 : τ _, (Obj C))))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ _ : τ (@FiniteArrowTail C Q zero A0 B0 f0), B0)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ n0) A0 B0 f0),
        rec B0 (@finite_arrow_tail_next C Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow C Q n0 A0 B0 f0 xs0)
          (@finite_arrow_tail_rest C Q n0 A0 B0 f0 xs0))
    n) A B f xs;

symbol finite_arrow_tail_last_arrow
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q n A B f))
  : τ (Hom C (@finite_arrow_tail_last_source C Q n A B f xs) (@finite_arrow_tail_last_target C Q n A B f xs))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
        @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
          @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
            @Pi_grpd (@FiniteArrowTail C Q n0 A0 B0 f0) (λ xs0 : τ _, Hom C (@finite_arrow_tail_last_source C Q n0
              A0 B0 f0 xs0) (@finite_arrow_tail_last_target C Q n0 A0 B0 f0 xs0))))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ _ : τ (@FiniteArrowTail C Q zero A0 B0 f0), f0)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ n0) A0 B0 f0),
        rec B0 (@finite_arrow_tail_next C Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow C Q n0 A0 B0 f0 xs0)
          (@finite_arrow_tail_rest C Q n0 A0 B0 f0 xs0))
    n) A B f xs;

symbol finite_arrow_tail_append
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n m : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q n A B f))
  (ys : τ (@FiniteArrowTail C Q m (@finite_arrow_tail_last_source C Q n A B f xs)
    (@finite_arrow_tail_last_target C Q n A B f xs) (@finite_arrow_tail_last_arrow C Q n A B f xs)))
  : τ (@FiniteArrowTail C Q (@nat_add n m) A B f)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
        @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
          @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
            @Pi_grpd (@FiniteArrowTail C Q n0 A0 B0 f0) (λ xs0 : τ _, @Function_grpd
              (@FiniteArrowTail C Q m (@finite_arrow_tail_last_source C Q n0 A0 B0 f0 xs0)
                (@finite_arrow_tail_last_target C Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_last_arrow C Q n0 A0 B0 f0
                xs0))
              (@FiniteArrowTail C Q (@nat_add n0 m) A0 B0 f0))))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ _ : τ (@FiniteArrowTail C Q zero A0 B0 f0),
      λ ys0 : τ (@FiniteArrowTail C Q m A0 B0 f0), ys0)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ n0) A0 B0 f0),
      λ ys0 : τ (@FiniteArrowTail C Q m
        (@finite_arrow_tail_last_source C Q (succ n0) A0 B0 f0 xs0) (@finite_arrow_tail_last_target C Q (succ n0) A0
          B0 f0 xs0) (@finite_arrow_tail_last_arrow C Q (succ n0) A0 B0 f0 xs0)),
        @finite_arrow_tail_cons C Q (@nat_add n0 m) A0 B0 f0
          (@finite_arrow_tail_next C Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow C Q n0 A0 B0 f0 xs0)
          (@finite_arrow_tail_step C Q n0 A0 B0 f0 xs0)
          (rec B0 (@finite_arrow_tail_next C Q n0 A0 B0 f0 xs0) (@finite_arrow_tail_arrow C Q n0 A0 B0 f0 xs0)
            (@finite_arrow_tail_rest C Q n0 A0 B0 f0 xs0) ys0))
    n) A B f xs ys;
