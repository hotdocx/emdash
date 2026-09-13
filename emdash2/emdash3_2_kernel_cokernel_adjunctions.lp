/* Whole kernel/cokernel adjunction structures for the preadditive setting.
   The only selected operation is an entire functor together with its native
   adjunction. No per-arrow W/V selection or factor/IsContr dictionary is an
   input. In this setting a selected terminal/initial object is a zero object.
   Existence of a particular whole structure is supplied, not inferred from
   arbitrary preadditivity or from matrix equations. */
require open emdash.emdash3_2_zero_arrow_diagrams;
require open emdash.emdash3_2_preadditive_categories;

// Whole kernel functor and its universal adjunction.
symbol KernelAdjunctionStructure [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) : Grpd
≔ `Σ_ K : τ (Functor (Functor_cat WalkingArrow_cat C) C),
    @Adjunction C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) K;

symbol kernel_adjunction_intro [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (K : τ (Functor (Functor_cat WalkingArrow_cat C) C))
  (J : τ (@Adjunction C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) K))
  : τ (@KernelAdjunctionStructure C S t T)
≔ Struct_sigma K J;

symbol kernel_adjunction_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (U : τ (@KernelAdjunctionStructure C S t T))
  : τ (Functor (Functor_cat WalkingArrow_cat C) C)
≔ sigma_Fst U;

symbol kernel_adjunction_evidence [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (U : τ (@KernelAdjunctionStructure C S t T))
  : τ (@Adjunction C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U))
≔ sigma_Snd U;

// Domain of the counit is the whole structural map.
symbol kernel_adjunction_inclusion [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (U : τ (@KernelAdjunctionStructure C S t T))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T U) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
≔ @fapp0
    (@Transf_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U))
      (@id_func (Functor_cat WalkingArrow_cat C)))
    (@Transf_cat (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T U) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
    (@comp_cat_cov_fapp1_func
      (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U))
      (@id_func (Functor_cat WalkingArrow_cat C)))
    (@counit_adj_transf C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U)
      (@kernel_adjunction_evidence C S t T U));

// Whole cokernel functor and its universal adjunction.
symbol CokernelAdjunctionStructure [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) : Grpd
≔ `Σ_ Q : τ (Functor (Functor_cat WalkingArrow_cat C) C),
    @Adjunction (Functor_cat WalkingArrow_cat C) C Q (@initial_arrow_diagram_func C t T);

symbol cokernel_adjunction_intro [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (Functor (Functor_cat WalkingArrow_cat C) C))
  (J : τ (@Adjunction (Functor_cat WalkingArrow_cat C) C Q (@initial_arrow_diagram_func C t T)))
  : τ (@CokernelAdjunctionStructure C S t T)
≔ Struct_sigma Q J;

symbol cokernel_adjunction_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (U : τ (@CokernelAdjunctionStructure C S t T))
  : τ (Functor (Functor_cat WalkingArrow_cat C) C)
≔ sigma_Fst U;

symbol cokernel_adjunction_evidence [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (U : τ (@CokernelAdjunctionStructure C S t T))
  : τ (@Adjunction (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) (@initial_arrow_diagram_func C t T))
≔ sigma_Snd U;

// Codomain of the unit is the whole structural map.
symbol cokernel_adjunction_projection [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (U : τ (@CokernelAdjunctionStructure C S t T))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T U))
≔ @fapp0
    (@Transf_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@id_func (Functor_cat WalkingArrow_cat C))
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_func C S t T U)))
    (@Transf_cat (Functor_cat WalkingArrow_cat C) C
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@cokernel_adjunction_func C S t T U))
    (@comp_cat_cov_fapp1_func
      (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
      (@id_func (Functor_cat WalkingArrow_cat C))
      (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_func C S t T U)))
    (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T U) (@initial_arrow_diagram_func C t T)
      (@cokernel_adjunction_evidence C S t T U));
