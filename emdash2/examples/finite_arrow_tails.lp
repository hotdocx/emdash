/* Generic beta, append and genuine boundary non-collapse. */
require open emdash.emdash3_2_finite_arrow_tail_append;
constant symbol C : Cat;
constant symbol Q : Π A : τ (Obj C), Π B : τ (Obj C), Π D : τ (Obj C),
  τ (Hom C A B) → τ (Hom C B D) → Grpd;
constant symbol A : τ (Obj C);
constant symbol B : τ (Obj C);
constant symbol D : τ (Obj C);
constant symbol E : τ (Obj C);
constant symbol f : τ (Hom C A B);
constant symbol g : τ (Hom C B D);
constant symbol h : τ (Hom C D E);
constant symbol q : τ (Q A B D f g);
constant symbol r : τ (Q B D E g h);
constant symbol q_other : τ (Q A B D f g);
symbol first ≔ @finite_arrow_tail_cons C Q zero A B f D g q
  (@finite_arrow_tail_nil C Q B D g);
symbol second ≔ @finite_arrow_tail_cons C Q zero B D g E h r
  (@finite_arrow_tail_nil C Q D E h);
symbol joined ≔ @finite_arrow_tail_append C Q (succ zero) (succ zero) A B f first second;

assert ⊢ @finite_arrow_tail_next C Q zero A B f first ≡ D;
assert ⊢ @finite_arrow_tail_arrow C Q zero A B f first ≡ g;
assert ⊢ @finite_arrow_tail_step C Q zero A B f first ≡ q;
assert ⊢ @finite_arrow_tail_last_source C Q (succ zero) A B f first ≡ B;
assert ⊢ @finite_arrow_tail_last_target C Q (succ zero) A B f first ≡ D;
assert ⊢ @finite_arrow_tail_last_arrow C Q (succ zero) A B f first ≡ g;
assert ⊢ @finite_arrow_tail_step C Q (succ zero) A B f joined ≡ q;
assert ⊢ @finite_arrow_tail_rest C Q (succ zero) A B f joined ≡ second;
assert ⊢ @finite_arrow_tail_last_arrow C Q (succ (succ zero)) A B f joined ≡ h;
assertnot ⊢ @finite_arrow_tail_step C Q zero A B f first ≡ q_other;
assertnot ⊢ @finite_arrow_tail_append C Q (succ zero) (succ zero) A B f first first
  : τ (@FiniteArrowTail C Q (succ (succ zero)) A B f);
