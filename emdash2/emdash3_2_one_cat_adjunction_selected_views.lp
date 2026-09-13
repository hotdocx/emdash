/* One-way realization comparisons for the newly derived ordinary records.
   They use new cancellation plus the two reconstruction equations. */
require open emdash.emdash3_2_one_cat_adjunction_records;
require open emdash.emdash3_2_kernel_adjunction_records;
require open emdash.emdash3_2_cokernel_adjunction_records;

symbol kernel_adjunction_record_lift_presentation_path [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S))
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C)) (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@= (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T (@kernel_presentation_structure C S t T W P)) d)) (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T (@kernel_presentation_structure C S t T W P) d) X e) (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d) X e))
≔ @kernel_adjunction_cancel_path C S C1 t T (@kernel_presentation_structure C S t T W P) X d (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T (@kernel_presentation_structure C S t T W P) d) X e) (@computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d) X e)
    (@eq_trans (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) _
      (@computational_kernel_lift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T (@kernel_presentation_structure C S t T W P) d) X e)
      (@eq_sym (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)
        (@computational_kernel_lift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_presentation_record C S t T W P d) X e)));

symbol cokernel_adjunction_record_lift_presentation_path [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalCokernels C S))
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T (@cokernel_presentation_structure C S t T W P)) d) X) (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T (@cokernel_presentation_structure C S t T W P) d) X e) (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) X e))
≔ @cokernel_adjunction_cancel_path C S C1 t T (@cokernel_presentation_structure C S t T W P) X d (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T (@cokernel_presentation_structure C S t T W P) d) X e) (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) X e)
    (@eq_trans (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) _ (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) _
      (@computational_cokernel_colift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T (@cokernel_presentation_structure C S t T W P) d) X e)
      (@eq_sym (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) _ (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)
        (@computational_cokernel_colift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_record C S t T W P d) X e)));
