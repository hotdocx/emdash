/* The inverse mate of Q⊣I realizes the original selected cokernel colift. */
require open emdash.emdash3_2_cokernel_adjunction_presentations;
require open emdash.emdash3_2_adjunction_mates;
require open emdash.emdash3_2_zero_arrow_universal_tests;

symbol cokernel_presentation_colift_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  : τ (Functor
      (Hom_cat (Functor_cat WalkingArrow_cat C) d
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))
      (Hom_cat C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X))
≔ @adjunction_untranspose_func (Functor_cat WalkingArrow_cat C) C
    (@cokernel_presentation_func C S t T W P) (@initial_arrow_diagram_func C t T)
    (@cokernel_presentation_adjunction C S t T W P) d X;

symbol cokernel_presentation_colift_semantic [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (W : τ (@HasComputationalCokernels C S))
  (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
  : τ (Hom C (@cokernel_presentation_selected_object C S W d) X)
≔ @computational_cokernel_colift C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X
    (@initial_arrow_cokernel_test C S t T X d h);

unif_rule
  @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $d $X)
    (@defiso_from _ _ _ (@Adjunction_hom_prof_comparison _ _ _ _
      (@cokernel_presentation_adjunction $C $S $t $T $W _)))) $h
  ≡ @sigma_Fst _ _ (@sigma_Fst _ _
      (@sigma_Snd _ _ (@sigma_Snd _ _ (@sigma_Snd _ _ $chosen))
        $Test (Struct_sigma $e _)))
  ↪ [ $chosen ≡ (@cokernel_presentation_selected $C $S $W $d);
      $Test ≡ $X;
      $e ≡ (@initial_arrow_test_outgoing $C $t $T $X $d $h) ];

// Dual point-first counit formula. Q need not be faithful, so the actual
// target diagram I(X) is checked rather than reconstructed from its Q-image.
unif_rule
  @comp_fapp0 _ _ _ _
    (@tapp0_fapp0 _ _ _ _ $X (@counit_adj_transf _ _ _ _
      (@cokernel_presentation_adjunction $C $S $t $T $W $P)))
    (@fapp1_fapp0 _ _ (@cokernel_presentation_func $C $S $t $T $W $P) $d $IX $h)
  ≡ @sigma_Fst _ _ (@sigma_Fst _ _
      (@sigma_Snd _ _ (@sigma_Snd _ _ (@sigma_Snd _ _ $chosen))
        $Test (Struct_sigma $e _)))
  ↪ [ $IX ≡ (@fapp0 $C (Functor_cat WalkingArrow_cat $C) (@initial_arrow_diagram_func $C $t $T) $X);
      $chosen ≡ (@cokernel_presentation_selected $C $S $W $d);
      $Test ≡ $X;
      $e ≡ (@initial_arrow_test_outgoing $C $t $T $X $d $h) ];

symbol cokernel_presentation_colift_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
  : τ (@= (Hom C (@cokernel_presentation_selected_object C S W d) X)
      (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h)
      (@cokernel_presentation_colift_semantic C S t T W d X h))
≔ @eq_refl (Hom C (@cokernel_presentation_selected_object C S W d) X)
    (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h);

symbol cokernel_presentation_colift_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
      (@comp_fapp0 C _ (@cokernel_presentation_selected_object C S W d) X
        (@fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X) h)
        (@computational_cokernel_morphism C S
          (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d)))
      (@initial_arrow_test_outgoing C t T X d h))
≔ @eq_trans (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) _ _ _
    (@eq_ap (Hom C (@cokernel_presentation_selected_object C S W d) X)
      (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
      (λ v : τ (Hom C (@cokernel_presentation_selected_object C S W d) X),
        @comp_fapp0 C _ (@cokernel_presentation_selected_object C S W d) X v
          (@computational_cokernel_morphism C S
            (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
            (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d)))
      _ _ (@cokernel_presentation_colift_path C S t T W P d X h))
    (@computational_cokernel_colift_path C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X
      (@initial_arrow_cokernel_test C S t T X d h));
