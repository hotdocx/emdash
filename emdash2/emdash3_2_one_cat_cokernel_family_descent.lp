/* Whole cokernel descent at the original diagram family, with reconstruction
   and uniqueness from native inverse mates. Whole zero-cell data is input;
   no per-object cone/factor dictionary or naturality premise is supplied. */
require open emdash.emdash3_2_one_cat_cokernel_family_inputs;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_paths;

// Apply the existing whole cokernel mate, indexed by D itself.
symbol one_cat_cokernel_family_descent [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  : τ (@Transf B C
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) Y)
≔ @fapp0 _ _ (@one_cat_adjunction_family_untranspose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1
    (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
    (@cokernel_adjunction_evidence C S t T0 Q) D Y)
    (@one_cat_cokernel_family_input B C C1 t T T0 D Y u z);

// Native reconstruction, with Q evaluated on the original diagram family.
symbol one_cat_cokernel_family_descent_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y) (@sym_transf_tapp0_transf
    B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
    Y) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y)
    (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) walking_arrow_tgt) u)
≔ @one_cat_cokernel_family_input_target_path B C C1 t T T0 D Y u z;

// The original whole target determines descent uniquely.
symbol one_cat_cokernel_family_descent_unique [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        Y)))
  (b : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)
    Y)) (p : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
    (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) Y) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
    WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) b) walking_arrow_tgt) u))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)
    Y) b (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z))
≔ @one_cat_cokernel_family_projection_reflect_path B C S C1 t T T0 Q Y D b (@one_cat_cokernel_family_descent B C S C1
  t T
  T0 Q D Y u z)
    (@eq_trans (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
      (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
      Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y) b) walking_arrow_tgt) u
      (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T0) Y) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
      Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y)
      (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) walking_arrow_tgt) p
      (@eq_sym (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y)
        (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) Y) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
        WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
        Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) D Y)
        (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z)) walking_arrow_tgt) u
        (@one_cat_cokernel_family_descent_reconstruction B C S C1 t T T0 Q D Y u z)));
