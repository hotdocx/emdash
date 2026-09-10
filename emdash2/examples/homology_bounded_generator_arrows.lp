/* Observe the original complete arrows without proof-valued result payloads. */
require open emdash.examples.homology_bounded_generator;
symbol manual2 ≔ @homology_row_fields_extend I C C1 P t Ab T T0 KP QP
  R0 R1 R2 f g z0 R3 h z1 x three generated1;
require open emdash.emdash3_2_finite_arrow_tail_arrows;

symbol generated_arrows ≔ @finite_arrow_tail_arrows C (@ComputationalExactArrowStep C P t (@computational_abelian_preabelian C P t Ab)) six _ _ _ generated2;
symbol manual_arrows ≔ @finite_arrow_tail_arrows C (@ComputationalExactArrowStep C P t (@computational_abelian_preabelian C P t Ab)) six _ _ _ manual2;
assert ⊢ generated_arrows : τ (@FiniteFamily (Obj (@LaxArrow_cat C)) (succ six));
assert ⊢ generated_arrows ≡ manual_arrows;
