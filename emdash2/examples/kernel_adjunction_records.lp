require open emdash.emdash3_2_kernel_adjunction_records;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @computational_kernel_object C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d)
  ≡ @fapp0 _ _ (@kernel_presentation_func C S t T W P) d;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) ⊢
  @computational_kernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d)
  ≡ @tapp0_fapp0 _ _ _ _ d (@kernel_presentation_inclusion C S t T W P);
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d) X e
  ≡ @kernel_presentation_test_lift C S W X d e;
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_kernel_lift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d) X e
  ≡ @kernel_record_lift_reconstruction C S t T W P d X e;
