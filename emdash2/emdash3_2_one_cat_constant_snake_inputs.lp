/* Constant raw triples enter the existing whole snake input before P/Q selection. */
require open emdash.emdash3_2_native_snake_inputs;
require open emdash.emdash3_2_one_cat_constant_chain_zeros;

// Existing constant-functor action carries the scalar triple-zero equation.
symbol one_cat_constant_triple_zero_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B X D : τ (Obj C)] (a : τ (Hom C A B)) (b : τ (Hom C B X)) (c : τ (Hom C X D))
  (z : τ (@= (Hom C A D) (@comp_fapp0 C A X D c (@comp_fapp0 C A B X b a))
    (@preadditive_hom_zero C S A D)))
  : τ (@= (@Transf K C (@Const_func K C A) (@Const_func K C D))
    (@comp_fapp0 (Functor_cat K C) (@Const_func K C A) (@Const_func K C X) (@Const_func K C D)
      (@Const_transf K C X D c)
      (@comp_fapp0 (Functor_cat K C) (@Const_func K C A) (@Const_func K C B) (@Const_func K C X)
        (@Const_transf K C B X b) (@Const_transf K C A B a)))
    (@zero_arrow_family_zero_transf K C t T T0 (@Const_func K C A) (@Const_func K C D)))
≔ @eq_trans _ _ _ _
    (@eq_ap (@Transf K C (@Const_func K C A) (@Const_func K C X))
      (@Transf K C (@Const_func K C A) (@Const_func K C D))
      (λ u, @comp_fapp0 (Functor_cat K C) (@Const_func K C A) (@Const_func K C X)
        (@Const_func K C D) (@Const_transf K C X D c) u) _ _
      (@eq_sym _ _ _ (@fapp1_comp_path C (Functor_cat K C) (@Const_func_func K C) A B X b a)))
    (@one_cat_constant_chain_zero_path K C S C1 t T T0 A X D (@comp_fapp0 C A B X b a) c z);

symbol one_cat_constant_native_snake_input [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B X D : τ (Obj C)] (a : τ (Hom C A B)) (b : τ (Hom C B X)) (c : τ (Hom C X D))
  (z : τ (@= (Hom C A D) (@comp_fapp0 C A X D c (@comp_fapp0 C A B X b a))
    (@preadditive_hom_zero C S A D)))
  : τ (@NativeSnakeInput K C t T (@Const_func K C A) (@Const_func K C B)
    (@Const_func K C X) (@Const_func K C D) (@Const_transf K C B X b) (@Const_transf K C X D c))
≔ @one_cat_native_snake_input K C C1 t T T0 (@Const_func K C A) (@Const_func K C B)
    (@Const_func K C X) (@Const_func K C D) (@Const_transf K C A B a) (@Const_transf K C B X b)
    (@Const_transf K C X D c) (@one_cat_constant_triple_zero_path K C S C1 t T T0 A B X D a b c z);

// The native source observation recovers the original whole constant arrow.
symbol one_cat_constant_native_snake_incoming_path [K C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B X D : τ (Obj C)] (a : τ (Hom C A B)) (b : τ (Hom C B X)) (c : τ (Hom C X D))
  (z : τ (@= (Hom C A D) (@comp_fapp0 C A X D c (@comp_fapp0 C A B X b a))
    (@preadditive_hom_zero C S A D)))
  : τ (@= (@Transf K C (@Const_func K C A) (@Const_func K C B))
    (@native_snake_incoming K C t T (@Const_func K C A) (@Const_func K C B)
      (@Const_func K C X) (@Const_func K C D) (@Const_transf K C B X b) (@Const_transf K C X D c)
      (@one_cat_constant_native_snake_input K C S C1 t T T0 A B X D a b c z))
    (@Const_transf K C A B a))
≔ @one_cat_native_snake_input_incoming_path K C C1 t T T0 (@Const_func K C A) (@Const_func K C B)
    (@Const_func K C X) (@Const_func K C D) (@Const_transf K C A B a) (@Const_transf K C B X b)
    (@Const_transf K C X D c) (@one_cat_constant_triple_zero_path K C S C1 t T T0 A B X D a b c z);
