/* Coherent point input needs no universal-operation data. */
require open emdash.emdash3_2_zero_arrow_family_point_inputs;
symbol K : Cat;
symbol C : Cat;
symbol t : τ (Obj C);
symbol T : τ (@TerminalObject C t);
symbol A : τ (Functor K C);
symbol D : τ (Functor K (Functor_cat WalkingArrow_cat C));
symbol h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D);
symbol x : τ (Obj K);
assert ⊢ @fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_family_point_input
  K C t T A D h x) ≡ @fapp0 K C A x;
assert ⊢ @fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@zero_arrow_family_point_input K C t T A D h x) ≡ @fapp0 K (Functor_cat WalkingArrow_cat C) D x;
assert ⊢ sigma_Snd (sigma_Snd (@zero_arrow_family_point_input K C t T A D h x)) ≡ (@tapp0_fapp0 K (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A) D x h);
