/* Pair observations preserve whole input reconstruction and existing arrow paths. */
require open emdash.emdash3_2_zero_arrow_pair_observations;
require open emdash.emdash3_2_one_cat_kernel_family_inputs;
require open emdash.emdash3_2_zero_arrow_family_action_paths;

symbol transf_arrow_pair_at [K C : Cat] [A B D : τ (Functor K C)]
  (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D)) (x : τ (Obj K))
  : τ (ArrowPairObservation C)
≔ Struct_sigma
    (@transf_arrow_observation_at K C (@lax_edge (Functor_cat K C) A B f) x)
    (@transf_arrow_observation_at K C (@lax_edge (Functor_cat K C) B D g) x);

// Compare the two existing parent presentations before substituting an input.
symbol zero_arrow_family_incoming_presentation_path [K C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Functor K C))
  (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf K C A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src))
    (@zero_arrow_family_incoming_transf K C t T A D h)
    (@sym_transf_tapp0_transf K WalkingArrow_cat C
      (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      D h walking_arrow_src))
≔ @eq_refl _ (@zero_arrow_family_incoming_transf K C t T A D h);

// Reframe the existing source law at the native incoming owner before evaluation.
symbol one_cat_kernel_input_incoming_path [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f)
    (@zero_arrow_family_zero_transf K C t T T0 A D)))
  : τ (@= (@Transf K C A B)
    (@zero_arrow_family_incoming_transf K C t T A (@transf_arrow_diagram_func K C B D g)
      (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z)) f)
≔ @eq_trans _ _ _ _
    (@zero_arrow_family_incoming_presentation_path K C t T A (@transf_arrow_diagram_func K C B D g)
      (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z))
    (@one_cat_kernel_family_input_source_path K C C1 t T T0 A
      (@transf_arrow_diagram_func K C B D g) f z);

// The existing whole source reconstruction supplies the only nontrivial path.
symbol one_cat_kernel_input_pair_path [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f)
    (@zero_arrow_family_zero_transf K C t T T0 A D)))
  (x : τ (Obj K))
  : τ (@= (ArrowPairObservation C)
    (@zero_arrow_family_pair_at K C t T A (@transf_arrow_diagram_func K C B D g)
      (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f z) x)
    (@transf_arrow_pair_at K C A B D f g x))
≔ @eq_ap (@Transf K C A B) (ArrowPairObservation C)
    (λ u, @transf_arrow_pair_at K C A B D u g x) _ _
    (@one_cat_kernel_input_incoming_path K C C1 t T T0 A B D f g z);

// Two complete-arrow interpretation paths give the path of the same pair.
symbol arrow_pair_observation_path [C : Cat]
  [a b a1 b1 : τ (Obj (@LaxArrow_cat C))]
  (p : τ (@= (Obj (@LaxArrow_cat C)) a a1))
  (q : τ (@= (Obj (@LaxArrow_cat C)) b b1))
  : τ (@= (ArrowPairObservation C) (Struct_sigma a b) (Struct_sigma a1 b1))
≔ @eq_trans _ _ _ _
    (@eq_ap (Obj (@LaxArrow_cat C)) (ArrowPairObservation C)
      (λ u, Struct_sigma u b) a a1 p)
    (@eq_ap (Obj (@LaxArrow_cat C)) (ArrowPairObservation C)
      (λ v, Struct_sigma a1 v) b b1 q);
