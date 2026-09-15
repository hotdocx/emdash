/* Native whole input for a general snake triple. The given h:J(A)⇒Arr(c∘b)
   retains its action and determines a; input formation selects no K or Q. */
require open emdash.emdash3_2_one_cat_kernel_family_inputs;
require open emdash.emdash3_2_one_cat_zero_family_paths;

symbol NativeSnakeInput [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A B X D : τ (Functor K C)) (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D)) : Grpd
≔ @Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b));

symbol native_snake_incoming [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c)) : τ (@Transf K C A B)
≔ @zero_arrow_family_incoming_transf K C t T A
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) h;

symbol native_snake_incoming_diagram [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c)) : τ (Functor K (Functor_cat WalkingArrow_cat C))
≔ @zero_arrow_family_incoming_func K C t T A
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) h;

// A whole triple-zero path enters through the existing native input constructor.
symbol one_cat_native_snake_input [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B X D : τ (Functor K C)] (a : τ (@Transf K C A B))
  (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (z : τ (@= (@Transf K C A D)
      (@comp_fapp0 (Functor_cat K C) A X D c (@comp_fapp0 (Functor_cat K C) A B X b a))
      (@zero_arrow_family_zero_transf K C t T T0 A D)))
  : τ (@NativeSnakeInput K C t T A B X D b c)
≔ @one_cat_kernel_family_input K C C1 t T T0 A
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) a
    (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) A B X D c b a)) z);

// Native whole source recovery returns the original arbitrary a.
symbol one_cat_native_snake_input_incoming_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B X D : τ (Functor K C)] (a : τ (@Transf K C A B))
  (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (z : τ (@= (@Transf K C A D)
      (@comp_fapp0 (Functor_cat K C) A X D c (@comp_fapp0 (Functor_cat K C) A B X b a))
      (@zero_arrow_family_zero_transf K C t T T0 A D)))
  : τ (@= (@Transf K C A B)
      (@native_snake_incoming K C t T A B X D b c
        (@one_cat_native_snake_input K C C1 t T T0 A B X D a b c z)) a)
≔ @one_cat_kernel_family_input_source_path K C C1 t T T0 A
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) a
    (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) A B X D c b a)) z);

// Associativity re-expresses the whole zero input as c∘(b∘a)=0.
symbol one_cat_native_snake_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C A D)
      (@comp_fapp0 (Functor_cat K C) A X D c
        (@comp_fapp0 (Functor_cat K C) A B X b (@native_snake_incoming K C t T A B X D b c h)))
      (@zero_arrow_family_zero_transf K C t T T0 A D))
≔ @eq_trans _ _ _ _
    (@comp_assoc (Functor_cat K C) A B X D c b (@native_snake_incoming K C t T A B X D b c h))
    (@one_cat_zero_family_chain_path K C C1 t T T0 A
      (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) h);
