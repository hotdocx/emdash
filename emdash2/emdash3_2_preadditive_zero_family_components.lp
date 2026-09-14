/* Observe the original whole zero through its terminal/initial factorization. */
require open emdash.emdash3_2_one_cat_zero_family_paths;
require open emdash.emdash3_2_additive_categories;

// Any outgoing arrow from the additive terminal object is zero.
symbol preadditive_zero_family_component_path [B C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@zero_arrow_family_zero_transf B C t T T0
  X Y)) (@preadditive_hom_zero C S (@fapp0 B C X b) (@fapp0 B C Y b)))
≔ @eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@zero_arrow_family_zero_transf B C t T
  T0 X Y)) (@comp_fapp0 C (@fapp0 B C X b) t (@fapp0 B C Y b) (@preadditive_hom_zero C S t (@fapp0 B C Y b))
  (@tapp0_fapp0 B C X (@Const_func B C t) b (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@preadditive_hom_zero C S (@fapp0 B C X b) (@fapp0 B C Y b))
    (@eq_ap (Hom C t (@fapp0 B C Y b)) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b))
      (λ h : τ (Hom C t (@fapp0 B C Y b)), @comp_fapp0 C (@fapp0 B C X b) t (@fapp0 B C Y b) h (@tapp0_fapp0 B C X
  (@Const_func B C t) b (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)))
      (@tapp0_fapp0 B C (@Const_func B C t) Y b (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@preadditive_hom_zero C S t (@fapp0 B C Y b))
      (@preadditive_terminal_to_zero_path C S t (@fapp0 B C Y b) T (@tapp0_fapp0 B C (@Const_func B C t) Y b
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
    (@preadditive_comp_zero_left_path C S (@fapp0 B C X b) t (@fapp0 B C Y b) (@tapp0_fapp0 B C X (@Const_func B C t)
  b (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));
