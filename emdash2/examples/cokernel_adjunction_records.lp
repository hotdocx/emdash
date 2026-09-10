require open emdash.emdash3_2_cokernel_adjunction_records;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢ @computational_cokernel_object C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) ≡ (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d);
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢ @computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) ≡ (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P));
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) X e
  ≡ @computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X e;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_cokernel_colift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) X e
  ≡ @cokernel_record_colift_reconstruction C S t T W P d X e;
