/* A data-only view of the original arrows, retaining each complete arrow in LaxArrow_cat. */
require open emdash.emdash3_2_finite_arrow_tails;
require open emdash.emdash3_2_finite_families;
require open emdash.emdash3_2_cubical_internalization;

symbol finite_arrow_tail_arrows
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n : τ Nat_grpd) [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (xs : τ (@FiniteArrowTail C Q n A B f))
  : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) (succ n))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (Obj C) (λ A0 : τ (Obj C),
      @Pi_grpd (Obj C) (λ B0 : τ (Obj C),
        @Pi_grpd (Hom C A0 B0) (λ f0 : τ (Hom C A0 B0),
          @Function_grpd (@FiniteArrowTail C Q n0 A0 B0 f0)
            (@FiniteFamily (Obj (@LaxArrow_cat C)) (succ n0))))))
    (λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ _ : τ (@FiniteArrowTail C Q zero A0 B0 f0),
        @finite_family_cons (Obj (@LaxArrow_cat C)) zero (@lax_edge C A0 B0 f0)
          (@finite_family_nil (Obj (@LaxArrow_cat C))))
    (λ n0 : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (Obj C), λ B0 : τ (Obj C), λ f0 : τ (Hom C A0 B0),
      λ xs0 : τ (@FiniteArrowTail C Q (succ n0) A0 B0 f0),
        @finite_family_cons (Obj (@LaxArrow_cat C)) (succ n0) (@lax_edge C A0 B0 f0)
          (rec B0 (@finite_arrow_tail_next C Q n0 A0 B0 f0 xs0)
            (@finite_arrow_tail_arrow C Q n0 A0 B0 f0 xs0)
            (@finite_arrow_tail_rest C Q n0 A0 B0 f0 xs0)))
    n) A B f xs;
