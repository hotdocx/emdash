/* Declaration-backed whole kernel over the original selected operation data.
   Presentation is additional coherent structure, not an automatically
   inhabited consequence of every old higher-categorical kernel family. */
require open emdash.emdash3_2_kernel_cokernel_adjunctions;
require open emdash.emdash3_2_strict_transfor_component_paths;
require open emdash.emdash3_2_kernel_maps;

// Read the original selection at the actual differential of the diagram.
symbol kernel_presentation_selected [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@ComputationalKernel C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ W (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator);

constant symbol KernelPresentation [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t))
  (W : τ (@HasComputationalKernels C S)) : Grpd;

injective symbol kernel_presentation_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  : τ (Functor (Functor_cat WalkingArrow_cat C) C);

injective symbol kernel_presentation_adjunction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  : τ (@Adjunction C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P));

// One-way adapter from the original selected presentation. The new whole
// adjunction interface itself has no selected W/V prerequisite.
symbol kernel_presentation_structure [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  : τ (@KernelAdjunctionStructure C S t T)
≔ @kernel_adjunction_intro C S t T
    (@kernel_presentation_func C S t T W P)
    (@kernel_presentation_adjunction C S t T W P);

// Proof-time object observation preserves K[d] as an adjunction discriminator.
unif_rule
  @fapp0 _ _ (@kernel_presentation_func $C $S _ _ $W _) $d
  ≡ @sigma_Fst _ _ $chosen
  ↪ [ $chosen ≡ (@kernel_presentation_selected $C $S $W $d) ];

// The actual whole inclusion is domain applied to the adjunction counit.
symbol kernel_presentation_inclusion [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@kernel_presentation_func C S t T W P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
≔ @kernel_adjunction_inclusion C S t T
    (@kernel_presentation_structure C S t T W P);

// Proof-time interpretation at the canonical unfolded counit component and
// selected-kernel projection. Endpoint/category slots are not discriminators.
unif_rule
  @tapp0_fapp0 _ _ _ _ $i
    (@tapp0_fapp0 _ _ _ _ $d
      (@counit_adj_transf _ _ _ _
        (@kernel_presentation_adjunction $C $S _ _ $W _)))
  ≡ @sigma_Fst _ _ (@sigma_Snd _ _ $chosen)
  ↪ [ $i ≡ walking_arrow_src;
      $chosen ≡ (@kernel_presentation_selected $C $S $W $d) ];

// Reusable agreement, derived by typed reflexivity through that usability rule.
symbol kernel_presentation_inclusion_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Hom C
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_presentation_inclusion C S t T W P))
      (@computational_kernel_morphism C S
        (@fapp0 WalkingArrow_cat C d walking_arrow_src)
        (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
        (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@kernel_presentation_selected C S W d)))
≔ @eq_refl (Hom C
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)
      (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@kernel_presentation_inclusion C S t T W P));

/* Map usability preserves whole K action and reuses the original selected lift. */


symbol kernel_presentation_selected_object [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S)) (d : τ (Functor WalkingArrow_cat C)) : τ (Obj C)
≔ @computational_kernel_object C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@kernel_presentation_selected C S W d);

symbol kernel_presentation_object_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Obj C) (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d)
      (@kernel_presentation_selected_object C S W d))
≔ @eq_refl (Obj C) (@fapp0 _ _ (@kernel_presentation_func C S t T W P) d);

// Actual strict naturality of eta supplies the existing precomposition
// factor, so no separate square/reconstruction input is added.
symbol kernel_presentation_map_semantic [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S))
  [d0 d1 : τ (Functor WalkingArrow_cat C)] (eta : τ (@Transf WalkingArrow_cat C d0 d1))
  : τ (Hom C (@kernel_presentation_selected_object C S W d0)
      (@kernel_presentation_selected_object C S W d1))
≔ @computational_kernel_map C S
    (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt)
    (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d0 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@fapp1_fapp0 WalkingArrow_cat C d1 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@kernel_presentation_selected C S W d0) (@kernel_presentation_selected C S W d1)
    (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src eta)
    (@hom_precomp_factor_intro C
      (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt)
      (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
      (@fapp1_fapp0 WalkingArrow_cat C d0 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@comp_fapp0 C _ _ _
        (@fapp1_fapp0 WalkingArrow_cat C d1 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src eta))
      (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_tgt eta)
      (@eq_sym _ _ _ (@strict_component_naturality_path WalkingArrow_cat C d0 d1 eta
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// The selected lift unfolds to two Sigma projections of its contractible
// factor space. Capture their inferred types, then check the exact semantic
// result as a side condition; do not pattern-match an alias or raw W application.
unif_rule
  @fapp1_fapp0 _ _ (@kernel_presentation_func $C $S _ _ $W _) $d0 $d1 $eta
  ≡ @sigma_Fst $A $B (@sigma_Fst $D $E $factor)
  ↪ [ (@sigma_Fst $A $B (@sigma_Fst $D $E $factor))
        ≡ (@kernel_presentation_map_semantic $C $S $W $d0 $d1 $eta) ];

symbol kernel_presentation_map_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [d0 d1 : τ (Functor WalkingArrow_cat C)] (eta : τ (@Transf WalkingArrow_cat C d0 d1))
  : τ (@= (Hom C (@kernel_presentation_selected_object C S W d0)
      (@kernel_presentation_selected_object C S W d1))
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0 d1 eta)
      (@kernel_presentation_map_semantic C S W d0 d1 eta))
≔ @eq_refl (Hom C (@kernel_presentation_selected_object C S W d0)
      (@kernel_presentation_selected_object C S W d1))
    (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d0 d1 eta);
