/* Remove the final arrow while retaining all earlier objects/arrows/annotations. */
require open emdash.emdash3_2_finite_arrow_tail_append;

symbol finite_arrow_tail_init
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q (succ n) A B f))
  : τ (@FiniteArrowTail C Q n A B f)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
      @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
        @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
          @Function_grpd (@FiniteArrowTail C Q (succ n0) A0 B0 f0)
            (@FiniteArrowTail C Q n0 A0 B0 f0)))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ _ : τ (@FiniteArrowTail C Q (succ zero) A0 B0 f0),
        @finite_arrow_tail_nil C Q A0 B0 f0)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ (succ n0)) A0 B0 f0),
        @finite_arrow_tail_cons C Q n0 A0 B0 f0
          (@finite_arrow_tail_next C Q (succ n0) A0 B0 f0 xs0)
          (@finite_arrow_tail_arrow C Q (succ n0) A0 B0 f0 xs0)
          (@finite_arrow_tail_step C Q (succ n0) A0 B0 f0 xs0)
          (rec B0 (@finite_arrow_tail_next C Q (succ n0) A0 B0 f0 xs0)
            (@finite_arrow_tail_arrow C Q (succ n0) A0 B0 f0 xs0)
            (@finite_arrow_tail_rest C Q (succ n0) A0 B0 f0 xs0)))
    n) A B f xs;

/* Reuse a property of the original penultimate object at the actual new endpoint.
   This proves no equality between objects and inserts no object cast. */
symbol finite_arrow_tail_init_endpoint_property
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (P : τ (Obj C) → Grpd)
  (n : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q (succ n) A B f))
  (p : τ (P (@finite_arrow_tail_last_source C Q (succ n) A B f xs)))
  : τ (P (@finite_arrow_tail_last_target C Q n A B f (@finite_arrow_tail_init C Q n A B f xs)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
      @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
        @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
          @Pi_grpd (@FiniteArrowTail C Q (succ n0) A0 B0 f0)
            (λ xs0 : τ (@FiniteArrowTail C Q (succ n0) A0 B0 f0),
              @Function_grpd
                (P (@finite_arrow_tail_last_source C Q (succ n0) A0 B0 f0 xs0))
                (P (@finite_arrow_tail_last_target C Q n0 A0 B0 f0
                  (@finite_arrow_tail_init C Q n0 A0 B0 f0 xs0))))))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ zero) A0 B0 f0), λ p0 : τ (P B0), p0)
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ (succ n0)) A0 B0 f0),
      λ p0 : τ (P (@finite_arrow_tail_last_source C Q (succ (succ n0)) A0 B0 f0 xs0)),
        rec B0 (@finite_arrow_tail_next C Q (succ n0) A0 B0 f0 xs0)
          (@finite_arrow_tail_arrow C Q (succ n0) A0 B0 f0 xs0)
          (@finite_arrow_tail_rest C Q (succ n0) A0 B0 f0 xs0) p0)
    n) A B f xs p;
