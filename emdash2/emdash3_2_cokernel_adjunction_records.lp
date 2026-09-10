/* Universal cokernel records derived from whole adjunction observations.
   Object and structural arrow are literal whole operations. The factor-space
   proof reuses the selected interpretation, with the computational centre
   explicitly fixed to the mate operation. No object/map transport, new
   primitive, rewrite or unification rule is introduced. Proof transport is
   confined to universality; its computational centre is explicitly installed. */
require open emdash.emdash3_2_cokernel_adjunction_mates;

// Object and projection are the actual whole Q/unit observations.
symbol cokernel_record_frame_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (@Σ_ (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q)) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P))) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (@cokernel_presentation_selected_object C S W d) (@computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d))))
≔ @eq_refl (@Σ_ (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q)) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)));

symbol cokernel_record_colift [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C))
  (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X)
≔ @fapp0 _ _ (@cokernel_presentation_colift_func C S t T W P d X)
    (@fapp0 _ _ (@adjunction_transpose_func (Functor_cat WalkingArrow_cat C) C
      (@cokernel_presentation_func C S t T W P) (@initial_arrow_diagram_func C t T)
      (@cokernel_presentation_adjunction C S t T W P) d X) (@computational_cokernel_colift C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X e));

// Compare the complete composable-arrow data, not the final runtime arrow.
symbol cokernel_record_composition_frame_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C)) (f : τ (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X))
  : τ (@= (@Σ_ (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X))) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X)) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@Product_pair_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d)) (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) f)) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X)) (@cokernel_presentation_selected_object C S W d) (@Product_pair_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@cokernel_presentation_selected_object C S W d)) (Hom C (@cokernel_presentation_selected_object C S W d) X) (@computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d)) f)))
≔ @eq_refl (@Σ_ (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X))) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X)) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@Product_pair_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d)) (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) f));

symbol cokernel_record_composition_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C)) (f : τ (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
      (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X f (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)))
      (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@cokernel_presentation_selected_object C S W d) X f (@computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d))))
≔ @eq_ap (@Σ_ (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X))) (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
    (λ frame : τ (@Σ_ (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X))), @comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (sigma_Fst frame) X
      (sigma_Snd (sigma_Snd frame)) (sigma_Fst (sigma_Snd frame)))
    (@Struct_sigma (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X)) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@Product_pair_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d)) (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) f)) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), @Product_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (Hom C Q X)) (@cokernel_presentation_selected_object C S W d) (@Product_pair_grpd (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@cokernel_presentation_selected_object C S W d)) (Hom C (@cokernel_presentation_selected_object C S W d) X) (@computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d)) f))
    (@cokernel_record_composition_frame_path C S t T W P d X f);

symbol cokernel_record_colift_reconstruction [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  (X : τ (Obj C))
  (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
      (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X
        (@cokernel_record_colift C S t T W P d X e) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)))
      (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))
≔ @eq_trans (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X) _ _ _
    (@cokernel_record_composition_path C S t T W P d X (@cokernel_record_colift C S t T W P d X e))
    (@computational_cokernel_colift_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X e);


symbol cokernel_record_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (@CokernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) X e)
≔ @Struct_sigma (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X)
    (λ u : τ (Hom C (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X), @= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) X)
      (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) X u (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)))
      (@cokernel_coannihilator_arrow C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X e))
    (@cokernel_record_colift C S t T W P d X e)
    (@cokernel_record_colift_reconstruction C S t T W P d X e);

symbol cokernel_record_universal [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C)) (X : τ (Obj C))
  (e : τ (@CokernelCoannihilator C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) X))
  : τ (IsContr (@CokernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) X e))
≔ @is_contr_recenter (@CokernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) X e)
    (@ind_eq (@Σ_ (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q)) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P))) (@Struct_sigma (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q) (@cokernel_presentation_selected_object C S W d) (@computational_cokernel_morphism C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d)))
      (@cokernel_record_frame_path C S t T W P d)
      (λ frame : τ (@Σ_ (Obj C) (λ Q : τ (Obj C), Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) Q)),
        IsContr (@CokernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
          (@terminal_arrow_test_outgoing C d) (sigma_Fst frame) (sigma_Snd frame) X e))
      (@computational_cokernel_factor_contr C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
        (@terminal_arrow_test_outgoing C d) (@cokernel_presentation_selected C S W d) X e))
    (@cokernel_record_factor C S t T W P d X e);

symbol cokernel_record_annihilation [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d))
      (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P)) (@terminal_arrow_test_outgoing C d))
      (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d)))
≔ @initial_arrow_test_chain_path C S t T (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) d
    (@tapp0_fapp0 _ _ _ _ d
      (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C
        (@cokernel_presentation_func C S t T W P) (@initial_arrow_diagram_func C t T)
        (@cokernel_presentation_adjunction C S t T W P)));

symbol cokernel_presentation_record [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)] [W : τ (@HasComputationalCokernels C S)]
  (P : τ (@CokernelPresentation C S t T W)) (d : τ (Functor WalkingArrow_cat C))
  : τ (@ComputationalCokernel C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d))
≔ @computational_cokernel_intro C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) (@terminal_arrow_test_outgoing C d)
    (@fapp0 _ _ (@cokernel_presentation_func C S t T W P) d) (@tapp0_fapp0 _ _ _ _ d (@cokernel_presentation_projection C S t T W P))
    (@cokernel_record_annihilation C S t T W P d)
    (@cokernel_record_universal C S t T W P d);
