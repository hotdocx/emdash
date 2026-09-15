/* Whole P/Q factors at the original diagrams, with their actual reconstructions. */
require open emdash.emdash3_2_one_cat_native_snake_factors;

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
symbol S : τ (@PreadditiveCategory C);
symbol P : τ (@KernelAdjunctionStructure C S t T);
symbol Q : τ (@CokernelAdjunctionStructure C S t T0);
symbol ac : τ (@Transf K C A B) ≔ @native_snake_incoming K C t T A B X D b c h;
symbol Fa : τ (Functor K (Functor_cat WalkingArrow_cat C)) ≔ @native_snake_incoming_diagram K C t T A B X D b c h;
symbol Fc : τ (Functor K (Functor_cat WalkingArrow_cat C)) ≔ @transf_arrow_diagram_func K C X D c;
symbol Kc : τ (Functor K C) ≔ @kernel_adjunction_family_func K C S t T P Fc;
symbol Qa : τ (Functor K C) ≔ @cokernel_adjunction_family_func K C S t T0 Q Fa;
symbol alpha : τ (@Transf K C A Kc) ≔ @one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h;
symbol gamma : τ (@Transf K C Qa D) ≔ @one_cat_native_snake_gamma K C S C1 t T T0 Q A B X D b c h;
symbol kappa : τ (@Transf K C Kc X) ≔ @kernel_adjunction_family_inclusion_transf K C S t T P Fc;
symbol pi : τ (@Transf K C B Qa) ≔ @cokernel_adjunction_family_projection_transf K C S t T0 Q Fa;

assert ⊢ alpha : τ (@Transf K C A Kc);
assert ⊢ gamma : τ (@Transf K C Qa D);
assert ⊢ @one_cat_native_snake_alpha_reconstruction K C S C1 t T T0 P A B X D b c h
  : τ (@= (@Transf K C A X) (@comp_fapp0 (Functor_cat K C) A Kc X kappa alpha) (@comp_fapp0 (Functor_cat K C) A B X b ac));
assert ⊢ @one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c h
  : τ (@= (@Transf K C B D) (@comp_fapp0 (Functor_cat K C) B Qa D gamma pi) (@comp_fapp0 (Functor_cat K C) B X D c b));
symbol x : τ (Obj K);
assert ⊢ @tapp0_fapp0 K C A Kc x alpha : τ (Hom C (@fapp0 K C A x) (@fapp0 K C Kc x));
assert ⊢ @tapp0_fapp0 K C Qa D x gamma : τ (Hom C (@fapp0 K C Qa x) (@fapp0 K C D x));
