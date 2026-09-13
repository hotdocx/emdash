/* Ordinary zero tests at the original arbitrary walking-arrow diagram.
   Compose the canonical raw input with the actual reconstruction comparison.
   No kernel/cokernel is selected, and the supplied diagram is not replaced
   by an equality cast or by a newly selected presentation. */
require open emdash.emdash3_2_one_cat_diagram_reconstruction;
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;

// The actual original d is the target; no diagram object is replaced.
symbol terminal_diagram_test_transf [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (b : τ (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)))
  (zero : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) (@comp_fapp0 C X (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator) b)
    (@preadditive_hom_zero C S X (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))))
  : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d)
≔ @comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) (@walking_arrow_func C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)) d
    (@one_cat_diagram_reconstruction_to C C1 d)
    (@terminal_zero_composite_transf C S C1 t T X (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) b (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator) zero);

// Dually keep d as the actual source and compose its reconstruction inverse.
symbol initial_diagram_test_transf [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (b : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X))
  (zero : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) X) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X b (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) X)))
  : τ (@Transf WalkingArrow_cat C d (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))
≔ @comp_fapp0 (Functor_cat WalkingArrow_cat C) d (@walking_arrow_func C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)
    (@initial_zero_composite_transf C S C1 t T (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator) b zero)
    (@one_cat_diagram_reconstruction_from C C1 d);
