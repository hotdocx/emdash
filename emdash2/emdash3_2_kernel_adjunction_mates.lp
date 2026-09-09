/* The canonical adjunction mate realizes the original selected kernel lift. */
require open emdash.emdash3_2_kernel_adjunction_presentations;
require open emdash.emdash3_2_adjunction_mates;
require open emdash.emdash3_2_zero_arrow_universal_tests;

symbol kernel_presentation_lift_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor
      (Hom_cat (Functor_cat WalkingArrow_cat C)
        (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d)
      (Hom_cat C X (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)))
≔ @adjunction_transpose_func C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P)
    (@kernel_presentation_adjunction C S t T W P) X d;

// Original selected lift at a diagram-indexed annihilator test.
symbol kernel_presentation_test_lift [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (e : τ (@WeakKernelAnnihilator C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) X))
  : τ (Hom C X (@kernel_presentation_selected_object C S W d))
≔ @computational_kernel_lift C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X e;

symbol kernel_presentation_lift_semantic [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (W : τ (@HasComputationalKernels C S))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (Hom C X (@kernel_presentation_selected_object C S W d))
≔ @kernel_presentation_test_lift C S W X d
    (@terminal_arrow_kernel_test C S t T X d h);

// Kernel universality identifies the canonical mate with this selected lift.
// Match the selected operation and the test arrow. The factor-space carrier
// ignores the test's annihilation proof, and uniqueness identifies its lifts.
unif_rule
  @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X $d)
    (@defiso_to _ _ _ (@Adjunction_hom_prof_comparison _ _ _ _
      (@kernel_presentation_adjunction $C $S $t $T $W _)))) $h
  ≡ @sigma_Fst _ _ (@sigma_Fst _ _
      (@sigma_Snd _ _ (@sigma_Snd _ _ (@sigma_Snd _ _ $chosen))
        $Test (Struct_sigma $e _)))
  ↪ [ $chosen ≡ (@kernel_presentation_selected $C $S $W $d);
      $Test ≡ $X;
      $e ≡ (@terminal_arrow_test_incoming $C $t $T $X $d $h) ];

// The ordinary unit formula can be exposed first (for example by a whole
// natural-family construction). Keep its source-diagram guard explicit as a
// constraint: nonfaithful K does not reconstruct J(X) from K(J(X)).
// Match the selected lift operation and its arrow input, not the incidental
// annihilation proof. Kernel uniqueness makes the result independent of that
// proof, and avoids comparing large differently elaborated proof payloads.
unif_rule
  @comp_fapp0 _ _ _ _
    (@fapp1_fapp0 _ _ (@kernel_presentation_func $C $S $t $T $W $P) $JX $d $h)
    (@tapp0_fapp0 _ _ _ _ $X (@unit_adj_transf _ _ _ _
      (@kernel_presentation_adjunction $C $S $t $T $W $P)))
  ≡ @sigma_Fst _ _ (@sigma_Fst _ _
      (@sigma_Snd _ _ (@sigma_Snd _ _ (@sigma_Snd _ _ $chosen))
        $Test (Struct_sigma $e _)))
  ↪ [ $JX ≡ (@fapp0 $C (Functor_cat WalkingArrow_cat $C) (@terminal_arrow_diagram_func $C $t $T) $X);
      $chosen ≡ (@kernel_presentation_selected $C $S $W $d);
      $Test ≡ $X;
      $e ≡ (@terminal_arrow_test_incoming $C $t $T $X $d $h) ];

symbol kernel_presentation_lift_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (@= (Hom C X (@kernel_presentation_selected_object C S W d))
      (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h)
      (@kernel_presentation_lift_semantic C S t T W X d h))
≔ @eq_refl (Hom C X (@kernel_presentation_selected_object C S W d))
    (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h);

// Reconstruction uses the original embedding and original factor space.
symbol kernel_presentation_lift_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (@= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@comp_fapp0 C X (@kernel_presentation_selected_object C S W d) _
        (@computational_kernel_morphism C S
          (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d))
        (@fapp0 _ _ (@kernel_presentation_lift_func C S t T W P X d) h))
      (@terminal_arrow_test_incoming C t T X d h))
≔ @eq_trans (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src)) _ _ _
    (@eq_ap (Hom C X (@kernel_presentation_selected_object C S W d))
      (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (λ v : τ (Hom C X (@kernel_presentation_selected_object C S W d)),
        @comp_fapp0 C X (@kernel_presentation_selected_object C S W d) _
          (@computational_kernel_morphism C S
            (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
            (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d)) v)
      _ _ (@kernel_presentation_lift_path C S t T W P X d h))
    (@computational_kernel_lift_path C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@kernel_presentation_selected C S W d) X
      (@terminal_arrow_kernel_test C S t T X d h));
