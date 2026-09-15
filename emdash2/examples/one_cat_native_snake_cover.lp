/* Pre-Abelian covered-map reconstruction and component computation. */
require open emdash.emdash3_2_one_cat_native_snake_covered_map;

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

symbol G : τ (Functor K (Functor_cat WalkingArrow_cat C)) ≔ @one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h;
symbol E : τ (Functor K C) ≔ @one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h;
symbol Kg : τ (Functor K C) ≔ @kernel_adjunction_family_func K C S t T P G;
symbol j : τ (@Transf K C E B) ≔ @one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h;
symbol rho : τ (@Transf K C E Kg) ≔ @one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h;
symbol Fr : τ (Functor K (Functor_cat WalkingArrow_cat C)) ≔ @transf_arrow_diagram_func K C E Kg rho;
symbol Falpha : τ (Functor K (Functor_cat WalkingArrow_cat C)) ≔ @one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h;
symbol Qalpha : τ (Functor K C) ≔ @cokernel_adjunction_family_func K C S t T0 Q Falpha;
symbol lift : τ (@Transf K C E Kc) ≔ @one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h;
symbol theta : τ (@Transf K C E Qalpha) ≔ @one_cat_native_snake_covered_transf K C S C1 t T T0 P Q A B X D b c h;
symbol qalpha : τ (@Transf K C Kc Qalpha) ≔ @cokernel_adjunction_family_projection_transf K C S t T0 Q Falpha;

assert ⊢ @one_cat_native_snake_cover_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C E Qa)
      (@comp_fapp0 (Functor_cat K C) E Kg Qa (@kernel_adjunction_family_inclusion_transf K C S t T P G) rho)
      (@comp_fapp0 (Functor_cat K C) E B Qa pi j));
assert ⊢ @one_cat_native_snake_covered_lift_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C E X) (@comp_fapp0 (Functor_cat K C) E Kc X kappa lift) (@comp_fapp0 (Functor_cat K C) E B X b j));
assert ⊢ theta : τ (@Transf K C E Qalpha);
assert ⊢ theta ≡ @comp_fapp0 (Functor_cat K C) E Kc Qalpha qalpha lift;
symbol x : τ (Obj K);
assert ⊢ @tapp0_fapp0 K C E Qalpha x theta
  ≡ @comp_fapp0 C (@fapp0 K C E x) (@fapp0 K C Kc x) (@fapp0 K C Qalpha x)
      (@tapp0_fapp0 K C Kc Qalpha x qalpha) (@tapp0_fapp0 K C E Kc x lift);
