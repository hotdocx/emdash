/* Cokernel presentation over the original selected cokernels. Its witness
   supplies coherent structure; no automatic introduction from old data. */
require open emdash.emdash3_2_kernel_cokernel_adjunctions;
require open emdash.emdash3_2_strict_transfor_component_paths;
require open emdash.emdash3_2_cokernel_maps;

symbol cokernel_presentation_selected [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalCokernels C S)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@ComputationalCokernel C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ W (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator);

constant symbol CokernelPresentation [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  (W : τ (@HasComputationalCokernels C S)) : Grpd;

injective symbol cokernel_presentation_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W))
  : τ (Functor (Functor_cat WalkingArrow_cat C) C);

injective symbol cokernel_presentation_adjunction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W))
  : τ (@Adjunction (Functor_cat WalkingArrow_cat C) C
      (@cokernel_presentation_func C S t T W P) (@initial_arrow_diagram_func C t T));

// One-way adapter from the original selected presentation. The new whole
// adjunction interface itself has no selected W/V prerequisite.
symbol cokernel_presentation_structure [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W))
  : τ (@CokernelAdjunctionStructure C S t T)
≔ @cokernel_adjunction_intro C S t T
    (@cokernel_presentation_func C S t T W P)
    (@cokernel_presentation_adjunction C S t T W P);

// Proof-time object observation retains Q[d] for adjunction cuts.
unif_rule
  @fapp0 _ _ (@cokernel_presentation_func $C $S _ _ $W _) $d
  ≡ @sigma_Fst _ _ $chosen
  ↪ [ $chosen ≡ (@cokernel_presentation_selected $C $S $W $d) ];

// The actual whole projection is codomain applied to the adjunction unit.
symbol cokernel_presentation_projection [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_presentation_func C S t T W P))
≔ @cokernel_adjunction_projection C S t T
    (@cokernel_presentation_structure C S t T W P);

unif_rule
  @tapp0_fapp0 _ _ _ _ $i
    (@tapp0_fapp0 _ _ _ _ $d
      (@unit_adj_transf _ _ _ _
        (@cokernel_presentation_adjunction $C $S _ _ $W _)))
  ≡ @sigma_Fst _ _ (@sigma_Snd _ _ $chosen)
  ↪ [ $i ≡ walking_arrow_tgt;
      $chosen ≡ (@cokernel_presentation_selected $C $S $W $d) ];

symbol cokernel_presentation_projection_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_presentation_func C S t T W P) d))
      (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_presentation_projection C S t T W P))
      (@computational_cokernel_morphism C S
        (@fapp0 WalkingArrow_cat C d walking_arrow_src)
        (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
        (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@cokernel_presentation_selected C S W d)))
≔ @eq_refl (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_presentation_func C S t T W P) d))
    (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ d (@cokernel_presentation_projection C S t T W P));

/* Map usability preserves whole Q action and reuses the original selected colift. */


symbol cokernel_presentation_selected_object [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalCokernels C S)) (d : τ (Functor WalkingArrow_cat C)) : τ (Obj C)
≔ @computational_cokernel_object C S
    (@fapp0 WalkingArrow_cat C d walking_arrow_src)
    (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@cokernel_presentation_selected C S W d);

symbol cokernel_presentation_object_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Obj C) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d)
      (@cokernel_presentation_selected_object C S W d))
≔ @eq_refl (Obj C) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d);

// Actual strict naturality of eta supplies the existing postcomposition
// factor, so no separate square/reconstruction input is added.
symbol cokernel_presentation_map_semantic [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalCokernels C S))
  [d0 d1 : τ (Functor WalkingArrow_cat C)] (eta : τ (@Transf WalkingArrow_cat C d0 d1))
  : τ (Hom C (@cokernel_presentation_selected_object C S W d0)
      (@cokernel_presentation_selected_object C S W d1))
≔ @computational_cokernel_map C S
    (@fapp0 WalkingArrow_cat C d0 walking_arrow_src) (@fapp0 WalkingArrow_cat C d0 walking_arrow_tgt)
    (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
    (@fapp1_fapp0 WalkingArrow_cat C d0 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@fapp1_fapp0 WalkingArrow_cat C d1 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@cokernel_presentation_selected C S W d0) (@cokernel_presentation_selected C S W d1)
    (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_tgt eta)
    (@hom_postcomp_factor_intro C
      (@fapp0 WalkingArrow_cat C d1 walking_arrow_src) (@fapp0 WalkingArrow_cat C d1 walking_arrow_tgt)
      (@fapp0 WalkingArrow_cat C d0 walking_arrow_src)
      (@fapp1_fapp0 WalkingArrow_cat C d1 walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@comp_fapp0 C _ _ _
        (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_tgt eta)
        (@fapp1_fapp0 WalkingArrow_cat C d0 walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@tapp0_fapp0 WalkingArrow_cat C d0 d1 walking_arrow_src eta)
      (@strict_component_naturality_path WalkingArrow_cat C d0 d1 eta
        walking_arrow_src walking_arrow_tgt walking_arrow_generator));

// The selected colift unfolds to two Sigma projections of its contractible
// factor space. Capture their inferred types, then check the exact semantic
// result as a side condition; do not pattern-match an alias or raw W application.
unif_rule
  @fapp1_fapp0 _ _ (@cokernel_presentation_func $C $S _ _ $W _) $d0 $d1 $eta
  ≡ @sigma_Fst $A $B (@sigma_Fst $D $E $factor)
  ↪ [ (@sigma_Fst $A $B (@sigma_Fst $D $E $factor))
        ≡ (@cokernel_presentation_map_semantic $C $S $W $d0 $d1 $eta) ];

symbol cokernel_presentation_map_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W))
  [d0 d1 : τ (Functor WalkingArrow_cat C)] (eta : τ (@Transf WalkingArrow_cat C d0 d1))
  : τ (@= (Hom C (@cokernel_presentation_selected_object C S W d0)
      (@cokernel_presentation_selected_object C S W d1))
      (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_presentation_func C S t T W P) d0 d1 eta)
      (@cokernel_presentation_map_semantic C S W d0 d1 eta))
≔ @eq_refl (Hom C (@cokernel_presentation_selected_object C S W d0)
      (@cokernel_presentation_selected_object C S W d1))
    (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_presentation_func C S t T W P) d0 d1 eta);
