/* General whole input, including arbitrary a and a zero final arrow.
   No monicity/epicity or universal selections are supplied in this file. */
require open emdash.emdash3_2_native_snake_inputs;
require open emdash.emdash3_2_one_cat_kernel_pullback_lifts;

symbol K : Cat;
symbol C : Cat;
symbol C1 : τ (IsNCat (cat_succ cat_zero) C);
symbol t : τ (Obj C);
symbol T : τ (@TerminalObject C t);
symbol T0 : τ (@TerminalObject (Op_cat C) t);
symbol A : τ (Functor K C);
symbol B : τ (Functor K C);
symbol X : τ (Functor K C);
symbol D : τ (Functor K C);
symbol a : τ (@Transf K C A B);
symbol b : τ (@Transf K C B X);
symbol c : τ (@Transf K C X D);
symbol h : τ (@NativeSnakeInput K C t T A B X D b c);

assert ⊢ @NativeSnakeInput K C t T A B X D b c
  ≡ @Transf K (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b));
assert ⊢ @native_snake_incoming K C t T A B X D b c h : τ (@Transf K C A B);
assert ⊢ @native_snake_incoming_diagram K C t T A B X D b c h
  ≡ @transf_arrow_diagram_func K C A B (@native_snake_incoming K C t T A B X D b c h);
assert ⊢ @one_cat_native_snake_zero K C C1 t T T0 A B X D b c h
  : τ (@= (@Transf K C A D)
      (@comp_fapp0 (Functor_cat K C) A X D c (@comp_fapp0 (Functor_cat K C) A B X b (@native_snake_incoming K C t T A B X D b c h)))
      (@zero_arrow_family_zero_transf K C t T T0 A D));

symbol z : τ (@= (@Transf K C A D)
  (@comp_fapp0 (Functor_cat K C) A X D c (@comp_fapp0 (Functor_cat K C) A B X b a))
  (@zero_arrow_family_zero_transf K C t T T0 A D));
assert ⊢ @one_cat_native_snake_input K C C1 t T T0 A B X D a b c z
  : τ (@NativeSnakeInput K C t T A B X D b c);
assert ⊢ @one_cat_native_snake_input_incoming_path K C C1 t T T0 A B X D a b c z
  : τ (@= (@Transf K C A B) (@native_snake_incoming K C t T A B X D b c
      (@one_cat_native_snake_input K C C1 t T T0 A B X D a b c z)) a);

symbol c0 : τ (@Transf K C X D) ≔ @zero_arrow_family_zero_transf K C t T T0 X D;
symbol z0 : τ (@= (@Transf K C A D)
  (@comp_fapp0 (Functor_cat K C) A X D c0 (@comp_fapp0 (Functor_cat K C) A B X b a))
  (@zero_arrow_family_zero_transf K C t T T0 A D))
≔ @one_cat_zero_family_precompose_path K C C1 t T T0 A X D (@comp_fapp0 (Functor_cat K C) A B X b a);
assert ⊢ @one_cat_native_snake_input K C C1 t T T0 A B X D a b c0 z0
  : τ (@NativeSnakeInput K C t T A B X D b c0);
assert ⊢ @one_cat_native_snake_input_incoming_path K C C1 t T T0 A B X D a b c0 z0
  : τ (@= (@Transf K C A B) (@native_snake_incoming K C t T A B X D b c0
      (@one_cat_native_snake_input K C C1 t T T0 A B X D a b c0 z0)) a);
