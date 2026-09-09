/* Actual terminal/initial arrow-diagram transformations supply the old
   annihilator inputs. No user-supplied square field or directed-cell reversal. */
require open emdash.emdash3_2_zero_arrow_diagrams;
require open emdash.emdash3_2_kernels_cokernels;
require open emdash.emdash3_2_strict_transfor_component_paths;

symbol terminal_arrow_test_incoming [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_src))
≔ @tapp0_fapp0 WalkingArrow_cat C _ d walking_arrow_src h;

symbol terminal_arrow_test_tip [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (Hom C t (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
≔ @tapp0_fapp0 WalkingArrow_cat C _ d walking_arrow_tgt h;

symbol terminal_arrow_test_outgoing [C : Cat] (d : τ (Functor WalkingArrow_cat C))
  : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src)
      (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
≔ @fapp1_fapp0 WalkingArrow_cat C d walking_arrow_src walking_arrow_tgt walking_arrow_generator;

// Existing global strict naturality compares the two cuts of h[generator].
symbol terminal_arrow_test_naturality_path [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (@= (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
      (@comp_fapp0 C _ _ _ (@terminal_arrow_test_outgoing C d) (@terminal_arrow_test_incoming C t T A d h))
      (@comp_fapp0 C A t _ (@terminal_arrow_test_tip C t T A d h) (@terminal_arrow_fapp0 C t T A)))
≔ @strict_component_naturality_path WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d
    h walking_arrow_src walking_arrow_tgt walking_arrow_generator;

// Initiality of a terminal object in a preadditive category supplies the
// zero comparison; no separately selected whole initial structure is assumed.
symbol terminal_arrow_test_chain_path [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (@= (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
      (@comp_fapp0 C _ _ _ (@terminal_arrow_test_outgoing C d) (@terminal_arrow_test_incoming C t T A d h))
      (@preadditive_hom_zero C S A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))
≔ @eq_trans (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) _ _ _
    (@terminal_arrow_test_naturality_path C t T A d h)
    (@eq_trans (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)) _ _ _
      (@eq_ap (Hom C t (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
        (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
        (λ q : τ (Hom C t (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)),
          @comp_fapp0 C A t _ q (@terminal_arrow_fapp0 C t T A)) _ _
        (@preadditive_terminal_to_zero_path C S t
          (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) T (@terminal_arrow_test_tip C t T A d h)))
      (@preadditive_comp_zero_left_path C S A t (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
        (@terminal_arrow_fapp0 C t T A)));

symbol terminal_arrow_kernel_test [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) d))
  : τ (@WeakKernelAnnihilator C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) A)
≔ @Struct_sigma (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_src))
    (λ e : τ (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_src)),
      @= (Hom C A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt))
        (@comp_fapp0 C A _ _ (@terminal_arrow_test_outgoing C d) e)
        (@preadditive_hom_zero C S A (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)))
    (@terminal_arrow_test_incoming C t T A d h)
    (@terminal_arrow_test_chain_path C S t T A d h);

// Initiality controls the endomorphisms of t, without needing a new
// opposite preadditive structure or any reverse to an arbitrary arrow.
// Native carrier annotation avoids premature injective-Hom decomposition
// of Hom(Op(C),t,t) versus Hom(C,t,t); their endomorphism carriers coincide.
symbol preadditive_initial_identity_zero_path [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t))
  : τ (@= (Obj (Hom_cat C t t)) (@id C t) (@preadditive_hom_zero C S t t))
≔ @eq_trans (Obj (Hom_cat C t t)) (@id C t)
    (@is_contr_center (Obj (Hom_cat C t t)) (@terminal_hom_contr (Op_cat C) t T t))
    (@preadditive_hom_zero C S t t)
    (@eq_sym (Obj (Hom_cat C t t)) _ _
      (@is_contr_path (Obj (Hom_cat C t t)) (@terminal_hom_contr (Op_cat C) t T t) (@id C t)))
    (@is_contr_path (Obj (Hom_cat C t t)) (@terminal_hom_contr (Op_cat C) t T t)
      (@preadditive_hom_zero C S t t));

symbol preadditive_initial_incoming_zero_path [C : Cat] (S : τ (@PreadditiveCategory C))
  [t A : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (f : τ (Hom C A t))
  : τ (@= (Hom C A t) f (@preadditive_hom_zero C S A t))
≔ @eq_trans (Hom C A t) f (@comp_fapp0 C A t t (@id C t) f)
    (@preadditive_hom_zero C S A t) (eq_refl f)
    (@eq_trans (Hom C A t) _ _ _
      (@eq_ap (Hom C t t) (Hom C A t) (λ e : τ (Hom C t t), @comp_fapp0 C A t t e f)
        (@id C t) (@preadditive_hom_zero C S t t)
        (@preadditive_initial_identity_zero_path C S t T))
      (@preadditive_comp_zero_left_path C S A t t f));

symbol initial_arrow_test_outgoing [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) A)
≔ @tapp0_fapp0 WalkingArrow_cat C d _ walking_arrow_tgt h;

symbol initial_arrow_test_tip [C : Cat] [t : τ (Obj C)]
  (T : τ (@TerminalObject (Op_cat C) t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) t)
≔ @tapp0_fapp0 WalkingArrow_cat C d _ walking_arrow_src h;

symbol initial_arrow_test_chain_path [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) A)
      (@comp_fapp0 C _ _ _ (@initial_arrow_test_outgoing C t T A d h) (@terminal_arrow_test_outgoing C d))
      (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) A))
≔ @eq_trans (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) A) _ _ _
    (@eq_sym _ _ _ (@strict_component_naturality_path WalkingArrow_cat C d
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)
      h walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@eq_trans (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) A) _ _ _
      (@eq_ap (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) t)
        (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) A)
        (λ q : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) t),
          @comp_fapp0 C _ t A (@initial_arrow_fapp0 C t T A) q) _ _
        (@preadditive_initial_incoming_zero_path C S t (@fapp0 WalkingArrow_cat C d walking_arrow_src)
          T (@initial_arrow_test_tip C t T A d h)))
      (@preadditive_comp_zero_right_path C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) t A
        (@initial_arrow_fapp0 C t T A)));

symbol initial_arrow_cokernel_test [C : Cat] (S : τ (@PreadditiveCategory C))
  [t : τ (Obj C)] (T : τ (@TerminalObject (Op_cat C) t)) (A : τ (Obj C))
  (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C d
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (@CokernelCoannihilator C S
      (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) A)
≔ @Struct_sigma (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) A)
    (λ e : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) A),
      @= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) A)
        (@comp_fapp0 C _ _ A e (@terminal_arrow_test_outgoing C d))
        (@preadditive_hom_zero C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) A))
    (@initial_arrow_test_outgoing C t T A d h)
    (@initial_arrow_test_chain_path C S t T A d h);
