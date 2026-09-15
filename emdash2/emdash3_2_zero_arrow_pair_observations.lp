/* Observe the two arrows of the original whole zero input together.
   The input remains A,D,h, before any kernel/cokernel choice. */
require open emdash.emdash3_2_zero_arrow_family_observations;
require open emdash.emdash3_2_arrow_equivalence_observations;

symbol ArrowPairObservation (C : Cat) : Grpd
≔ @Σ_ (Obj (@LaxArrow_cat C)) (λ _ : τ (Obj (@LaxArrow_cat C)), Obj (@LaxArrow_cat C));

symbol zero_arrow_family_pair_at [K C : Cat] [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (A : τ (Functor K C)) (D : τ (Functor K (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (x : τ (Obj K)) : τ (ArrowPairObservation C)
≔ Struct_sigma
    (@transf_arrow_observation_at K C
      (@lax_edge (Functor_cat K C) A (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
        (@zero_arrow_family_incoming_transf K C t T A D h)) x)
    (@transf_arrow_observation_at K C
      (@lax_edge (Functor_cat K C) (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func K WalkingArrow_cat C D walking_arrow_tgt)
        (@diagram_family_transf K WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) x);

// Typed projections retain the compact observed-pair interface.
symbol arrow_pair_observation_incoming [C : Cat] (p : τ (ArrowPairObservation C))
  : τ (Obj (@LaxArrow_cat C)) ≔ sigma_Fst p;
symbol arrow_pair_observation_outgoing [C : Cat] (p : τ (ArrowPairObservation C))
  : τ (Obj (@LaxArrow_cat C)) ≔ sigma_Snd p;
