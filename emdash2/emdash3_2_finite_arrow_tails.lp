/*
  Indexed finite arrow-result tails.

  Starting at f : A → B, a length-n tail stores n further arrows and one
  Q-annotation at each of the n adjacent pairs. Each object and arrow is
  stored once. Rigid record indices retain n/A/B/f for LF reconstruction;
  the corresponding Nat/Sigma model and rejected transparent consumer are
  preserved in the bounded-assembly audit.

  Only constructor/projection beta is primitive here. This is result data,
  not a new category of complexes or a replacement for whole H/delta.
*/
require open emdash.emdash3_2_nat_arithmetic;

constant symbol FiniteArrowTail
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  (n : τ Nat_grpd) (A B : τ (Obj C)) (f : τ (Hom C A B)) : Grpd;

constant symbol finite_arrow_tail_nil
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  [A B : τ (Obj C)] [f : τ (Hom C A B)]
  : τ (@FiniteArrowTail C Q zero A B f);

constant symbol finite_arrow_tail_cons
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  [n : τ Nat_grpd] [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (D : τ (Obj C)) (g : τ (Hom C B D)) (step : τ (Q A B D f g))
  (rest : τ (@FiniteArrowTail C Q n B D g))
  : τ (@FiniteArrowTail C Q (succ n) A B f);

symbol finite_arrow_tail_next
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  [n : τ Nat_grpd] [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (tail : τ (@FiniteArrowTail C Q (succ n) A B f)) : τ (Obj C);
rule @finite_arrow_tail_next _ _ _ _ _ _
  (@finite_arrow_tail_cons _ _ _ _ _ _ $D _ _ _) ↪ $D;

symbol finite_arrow_tail_arrow
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  [n : τ Nat_grpd] [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (tail : τ (@FiniteArrowTail C Q (succ n) A B f))
  : τ (Hom C B (@finite_arrow_tail_next C Q n A B f tail));
rule @finite_arrow_tail_arrow _ _ _ _ _ _
  (@finite_arrow_tail_cons _ _ _ _ _ _ _ $g _ _) ↪ $g;

symbol finite_arrow_tail_step
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  [n : τ Nat_grpd] [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (tail : τ (@FiniteArrowTail C Q (succ n) A B f))
  : τ (Q A B (@finite_arrow_tail_next C Q n A B f tail) f
    (@finite_arrow_tail_arrow C Q n A B f tail));
rule @finite_arrow_tail_step _ _ _ _ _ _
  (@finite_arrow_tail_cons _ _ _ _ _ _ _ _ $q _) ↪ $q;

symbol finite_arrow_tail_rest
  [C : Cat]
  (Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
    τ (Hom C A B) → τ (Hom C B D) → Grpd)
  [n : τ Nat_grpd] [A B : τ (Obj C)] [f : τ (Hom C A B)]
  (tail : τ (@FiniteArrowTail C Q (succ n) A B f))
  : τ (@FiniteArrowTail C Q n B (@finite_arrow_tail_next C Q n A B f tail)
    (@finite_arrow_tail_arrow C Q n A B f tail));
rule @finite_arrow_tail_rest _ _ _ _ _ _
  (@finite_arrow_tail_cons _ _ _ _ _ _ _ _ _ $rest) ↪ $rest;
