/* Whole kernel inputs at the original diagram, using native square action.
   This is a whole-data input constructor; it supplies no kernel choice,
   per-object naturality fields or ordinary universal factor dictionary. */
require open emdash.emdash3_2_one_cat_cokernel_family_inputs;

// The original differential is precomposed as one whole transformation.
symbol precomposed_diagram_family_func [B C : Cat] (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C)))
  (p : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) : τ (Functor B
    (Functor_cat WalkingArrow_cat C))
≔ (@transf_arrow_diagram_func B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_fapp0
  (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) p));

// J(X)⇒Arr(u) from the whole annihilation cell u∘k=0.
symbol one_cat_kernel_family_introduced_input [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X A Y : τ (Functor B C)) (k : τ (@Transf B C X A)) (u : τ (@Transf B C A Y))
  (z : τ (@= (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X A Y u k) (@zero_arrow_family_zero_transf B C t T T0 X
    Y)))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) (@transf_arrow_diagram_func B C A Y u))
≔ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) (@transf_arrow_diagram_func B C X (@Const_func B C t)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@transf_arrow_diagram_func B C A Y u) (@sym_func_func_transf WalkingArrow_cat B C (@walking_arrow_func (Functor_cat
  B C) X (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@walking_arrow_func (Functor_cat B C) A Y u) (@one_cat_square_diagram_transf (Functor_cat
  B C) (@one_cat_functor_category B C C1) X A (@Const_func B C t) Y (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) u k (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@path_to_hom (Hom_cat (Functor_cat B C) X Y) (@zero_arrow_family_zero_transf B C t T T0 X
  Y) (@comp_fapp0 (Functor_cat B C) X A Y u k) (@eq_sym (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X A Y u k)
  (@zero_arrow_family_zero_transf B C t T T0 X Y) z)))) (@one_cat_diagram_family_reconstruction_from B C C1 (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X));

// Retain D itself as the target of the native kernel-mate input.
symbol one_cat_kernel_family_input [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (D : τ (Functor B
    (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) X) D)
≔ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D
  (@one_cat_diagram_family_reconstruction_to B C C1 D) (@one_cat_kernel_family_introduced_input B C C1 t T T0 X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) k (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) z);

// Whole source recovery for the introduced input.
symbol one_cat_kernel_family_introduced_source_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X A Y : τ (Functor B C)) (k : τ (@Transf B C X A)) (u : τ (@Transf B C A Y))
  (z : τ (@= (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X A Y u k) (@zero_arrow_family_zero_transf B C t T T0 X
    Y)))
  : τ (@= (@Transf B C X A) (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) (@transf_arrow_diagram_func B C A Y u)
    (@one_cat_kernel_family_introduced_input B C C1 t T T0 X A Y k u z) walking_arrow_src) k)
≔ @one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
      (@transf_arrow_diagram_func B C X (@Const_func B C t) (@diagram_family_transf B WalkingArrow_cat C
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) walking_arrow_src
      walking_arrow_tgt walking_arrow_generator)) (@transf_arrow_diagram_func B C A Y u) (@sym_func_func_transf
      WalkingArrow_cat B C (@walking_arrow_func (Functor_cat B C) X (@Const_func B C t) (@diagram_family_transf B
      WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@walking_arrow_func (Functor_cat B C) A Y u)
      (@one_cat_square_diagram_transf (Functor_cat B C) (@one_cat_functor_category B C C1) X A (@Const_func B C t) Y
      (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator) u k
      (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
      (@path_to_hom (Hom_cat (Functor_cat B C) X Y) (@zero_arrow_family_zero_transf B C t T T0 X Y) (@comp_fapp0
      (Functor_cat B C) X A Y u k) (@eq_sym (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X A Y u k)
      (@zero_arrow_family_zero_transf B C t T T0 X Y) z)))) (@one_cat_diagram_family_reconstruction_from B C C1 (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X));

// Reconstruction has identity endpoints, so source recovery retains k.
symbol one_cat_kernel_family_input_source_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (D : τ (Functor B
    (Functor_cat WalkingArrow_cat C)))
  (k : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (z : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0
    (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
    walking_arrow_tgt walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
    D (@one_cat_kernel_family_input B C C1 t T T0 X D k z) walking_arrow_src) k)
≔ @eq_trans (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D (@one_cat_kernel_family_input B C C1 t T T0 X D k z) walking_arrow_src)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) X) (@transf_arrow_diagram_func B C (@diagram_family_at_func B
      WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
      (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@one_cat_kernel_family_introduced_input B C C1 t T T0 X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) k (@diagram_family_transf
      B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) z) walking_arrow_src) k
    (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X)
        (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat
        C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) D (@one_cat_diagram_family_reconstruction_to B
        C C1 D) (@one_cat_kernel_family_introduced_input B C C1 t T T0 X (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) k
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        z))
    (@one_cat_kernel_family_introduced_source_path B C C1 t T T0 X (@diagram_family_at_func B WalkingArrow_cat C D
      walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) k (@diagram_family_transf
      B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) z);
