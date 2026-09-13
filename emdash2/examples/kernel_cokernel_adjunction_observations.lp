/* Whole-mate reconstruction on original raw inputs, without W/V. */
require open emdash.emdash3_2_kernel_cokernel_adjunction_observations;
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;

// The actual kernel mate reconstructs the original incoming arrow.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  [X A B : τ (Obj C)] (b : τ (Hom C X A)) (d : τ (Hom C A B))
  (zero : τ (@= (Hom C X B) (@comp_fapp0 C X A B d b)
    (@preadditive_hom_zero C S X B))) ⊢
  @kernel_adjunction_lift_reconstruction C S t T P X (@walking_arrow_func C A B d) (@terminal_zero_composite_transf C S C1 t T X A B b d zero)
  : τ (@= (Hom C X A) (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) A (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@walking_arrow_func C A B d) (@kernel_adjunction_inclusion C S t T P)) (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T P X (@walking_arrow_func C A B d)) (@terminal_zero_composite_transf C S C1 t T X A B b d zero))) b);

// Its structural map is annihilated by the original differential d.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  [X A B : τ (Obj C)] (b : τ (Hom C X A)) (d : τ (Hom C A B))
  (zero : τ (@= (Hom C X B) (@comp_fapp0 C X A B d b)
    (@preadditive_hom_zero C S X B))) ⊢
  @kernel_adjunction_annihilation C S t T P (@walking_arrow_func C A B d)
  : τ (@= (Hom C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) B) (@comp_fapp0 C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) A B d (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@walking_arrow_func C A B d) (@kernel_adjunction_inclusion C S t T P)))
    (@preadditive_hom_zero C S (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) B));

// The actual cokernel mate reconstructs the original outgoing arrow.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@CokernelAdjunctionStructure C S t T))
  [A B X : τ (Obj C)] (d : τ (Hom C A B)) (b : τ (Hom C B X))
  (zero : τ (@= (Hom C A X) (@comp_fapp0 C A B X b d)
    (@preadditive_hom_zero C S A X))) ⊢
  @cokernel_adjunction_colift_reconstruction C S t T P X (@walking_arrow_func C A B d) (@initial_zero_composite_transf C S C1 t T A B X d b zero)
  : τ (@= (Hom C B X) (@comp_fapp0 C B (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) X (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T P X (@walking_arrow_func C A B d)) (@initial_zero_composite_transf C S C1 t T A B X d b zero)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@walking_arrow_func C A B d) (@cokernel_adjunction_projection C S t T P))) b);

// Its structural map coannihilates the original differential d.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@CokernelAdjunctionStructure C S t T))
  [A B X : τ (Obj C)] (d : τ (Hom C A B)) (b : τ (Hom C B X))
  (zero : τ (@= (Hom C A X) (@comp_fapp0 C A B X b d)
    (@preadditive_hom_zero C S A X))) ⊢
  @cokernel_adjunction_annihilation C S t T P (@walking_arrow_func C A B d)
  : τ (@= (Hom C A (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) (@walking_arrow_func C A B d))) (@comp_fapp0 C A B (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@walking_arrow_func C A B d) (@cokernel_adjunction_projection C S t T P)) d)
    (@preadditive_hom_zero C S A (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) (@walking_arrow_func C A B d))));

// Reconstruction cannot silently replace the supplied incoming arrow.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  [X A B : τ (Obj C)] (b : τ (Hom C X A)) (d : τ (Hom C A B))
  (zero : τ (@= (Hom C X B) (@comp_fapp0 C X A B d b)
    (@preadditive_hom_zero C S X B))) (other : τ (Hom C X A)) ⊢
  @kernel_adjunction_lift_reconstruction C S t T P X (@walking_arrow_func C A B d) (@terminal_zero_composite_transf C S C1 t T X A B b d zero)
  : τ (@= (Hom C X A) (@comp_fapp0 C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) A (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@walking_arrow_func C A B d) (@kernel_adjunction_inclusion C S t T P)) (@fapp0 _ _ (@kernel_adjunction_lift_func C S t T P X (@walking_arrow_func C A B d)) (@terminal_zero_composite_transf C S C1 t T X A B b d zero))) other);

// Nor can the dual reconstruction replace the supplied outgoing arrow.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@CokernelAdjunctionStructure C S t T))
  [A B X : τ (Obj C)] (d : τ (Hom C A B)) (b : τ (Hom C B X))
  (zero : τ (@= (Hom C A X) (@comp_fapp0 C A B X b d)
    (@preadditive_hom_zero C S A X))) (other : τ (Hom C B X)) ⊢
  @cokernel_adjunction_colift_reconstruction C S t T P X (@walking_arrow_func C A B d) (@initial_zero_composite_transf C S C1 t T A B X d b zero)
  : τ (@= (Hom C B X) (@comp_fapp0 C B (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T P) (@walking_arrow_func C A B d)) X (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T P X (@walking_arrow_func C A B d)) (@initial_zero_composite_transf C S C1 t T A B X d b zero)) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@walking_arrow_func C A B d) (@cokernel_adjunction_projection C S t T P))) other);
