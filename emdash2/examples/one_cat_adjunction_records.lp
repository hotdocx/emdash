/* Derived records keep whole objects, structural maps, and actual mate centres.
   There are no W/V selections or supplied all-test factor dictionaries. */
require open emdash.emdash3_2_one_cat_adjunction_records;

// Literal whole object and structural arrow are retained.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @computational_kernel_object C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T U d) ≡ (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d);

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @computational_kernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T U d) ≡ (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U));

// Projecting the contraction centre returns the actual whole mate.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_kernel_lift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T U d) X e ≡ (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T U X d) (@terminal_diagram_test_transf C S C1 t T X d (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@weak_kernel_annihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)));

// The public reconstruction view has the original raw arrow as its target.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_kernel_lift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T U d) X e
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U)) (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T U X d) (@terminal_diagram_test_transf C S C1 t T X d (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@weak_kernel_annihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)))) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e));

// The public uniqueness view now follows from whole structure alone.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (U : τ (@KernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@WeakKernelAnnihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  (u : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d))) (p : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_adjunction_inclusion C S t T U)) u) (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))) ⊢
  @computational_kernel_lift_unique_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@kernel_adjunction_record C S C1 t T U d) X e u p
  : τ (@= (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)) (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T U X d) (@terminal_diagram_test_transf C S C1 t T X d (@weak_kernel_annihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@weak_kernel_annihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))) u);

// Literal whole object and structural arrow are retained.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @computational_cokernel_object C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T U d) ≡ (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d);

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) ⊢
  @computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T U d) ≡ (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U));

// Projecting the contraction centre returns the actual whole mate.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T U d) X e ≡ (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T U X d) (@initial_diagram_test_transf C S C1 t T X d (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@cokernel_coannihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e)));

// The public reconstruction view has the original raw arrow as its target.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X)) ⊢
  @computational_cokernel_colift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T U d) X e
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T U X d) (@initial_diagram_test_transf C S C1 t T X d (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@cokernel_coannihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U))) (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e));

// The public uniqueness view now follows from whole structure alone.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C)) (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  (u : τ (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X)) (p : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X u (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_adjunction_projection C S t T U))) (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))) ⊢
  @computational_cokernel_colift_unique_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_adjunction_record C S C1 t T U d) X e u p
  : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X) (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T U X d) (@initial_diagram_test_transf C S C1 t T X d (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e) (@cokernel_coannihilator_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))) u);
