/* The two observed arrows retain their original whole input and order. */
require open emdash.emdash3_2_zero_arrow_pair_observations;

assert [C : Cat] (a b : τ (Obj (@LaxArrow_cat C))) ⊢
  @arrow_pair_observation_incoming C (Struct_sigma a b) ≡ a;
assert [C : Cat] (a b : τ (Obj (@LaxArrow_cat C))) ⊢
  @arrow_pair_observation_outgoing C (Struct_sigma a b) ≡ b;
assertnot [C : Cat] (a b : τ (Obj (@LaxArrow_cat C))) ⊢
  @arrow_pair_observation_incoming C (Struct_sigma a b) ≡ b;

assert [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K)) ⊢
  @arrow_pair_observation_incoming C (@zero_arrow_family_pair_at K C t T A D h x)
  ≡ @lax_edge C (@fapp0 K C A x)
      (@fapp0 K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x)
      (@tapp0_fapp0 K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x
        (@zero_arrow_family_incoming_transf K C t T A D h));
assert [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K)) ⊢
  @arrow_pair_observation_outgoing C (@zero_arrow_family_pair_at K C t T A D h x)
  ≡ @lax_edge C (@fapp0 K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src) x)
      (@fapp0 K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) x)
      (@tapp0_fapp0 K C (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt) x
        (@diagram_family_transf K WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator));
assert [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K)) ⊢
  sigma_Fst (sigma_Snd (@arrow_pair_observation_incoming C (@zero_arrow_family_pair_at K C t T A D h x)))
  ≡ sigma_Fst (@arrow_pair_observation_outgoing C (@zero_arrow_family_pair_at K C t T A D h x));
