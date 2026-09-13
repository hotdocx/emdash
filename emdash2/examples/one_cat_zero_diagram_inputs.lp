/* Original-diagram input formation retains the actual raw arrows. */
require open emdash.emdash3_2_one_cat_zero_diagram_inputs;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (b : τ (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)))
  (zero : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (@comp_fapp0 C X (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator) b)
    (@preadditive_hom_zero C S X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))) ⊢
  @tapp0_fapp0 WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d walking_arrow_src
    (@terminal_diagram_test_transf C S C1 t T X d b zero) ≡ b;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (b : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X))
  (zero : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) X) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X b (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) X))) ⊢
  @tapp0_fapp0 WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X) walking_arrow_tgt
    (@initial_diagram_test_transf C S C1 t T X d b zero) ≡ b;
