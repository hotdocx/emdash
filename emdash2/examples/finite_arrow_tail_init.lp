/* Trimming keeps the original prefix and endpoint-property evidence. */
require open emdash.examples.finite_arrow_tails;
require open emdash.emdash3_2_finite_arrow_tail_init;

assert ⊢ @finite_arrow_tail_init C Q zero A B f first
  ≡ @finite_arrow_tail_nil C Q A B f;
assert ⊢ @finite_arrow_tail_init C Q (succ zero) A B f joined ≡ first;
assert ⊢ @finite_arrow_tail_step C Q zero A B f
  (@finite_arrow_tail_init C Q (succ zero) A B f joined) ≡ q;
constant symbol P : τ (Obj C) → Grpd;
constant symbol p : τ (P D);
assert ⊢ @finite_arrow_tail_init_endpoint_property C Q P (succ zero) A B f joined p ≡ p;
assertnot ⊢ @finite_arrow_tail_step C Q zero A B f
  (@finite_arrow_tail_init C Q (succ zero) A B f joined) ≡ q_other;
