/* Whole short-exact families as the actual native kernel-cokernel pair.
   The input is the original coherent h:J∘A⇒D. Its derived whole zero cell
   constructs γ; the existing H boundary is β. Invertibility of these two
   specific maps is supplied row structure. This introduces no splitting,
   ordinary factor dictionary, comparison primitive or exactness theorem. */
require open emdash.emdash3_2_one_cat_zero_family_paths;
require open emdash.emdash3_2_one_cat_cokernel_family_descent;
require open emdash.emdash3_2_homology_adjunction_families;

// Descend g through the original incoming F=Arr(f), using the internally derived whole zero cell.
symbol one_cat_row_cokernel_comparison [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt))
≔ @one_cat_cokernel_family_descent B C S C1 t T T0 Q (@zero_arrow_family_incoming_func B C t T A D h)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_zero_family_chain_path B C C1 t T T0 A D h);

// Native inverse mating reconstructs the original whole outgoing arrow.
symbol one_cat_row_cokernel_reconstruction_path [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))
      (@sym_transf_tapp0_transf B WalkingArrow_cat C (@zero_arrow_family_incoming_func B C t T A D h) (@comp_cat_fapp0
        B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B
        WalkingArrow_cat C D walking_arrow_tgt)) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func B (Functor_cat
        WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
        Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)
        (@zero_arrow_family_incoming_func B C t T A D h) (@diagram_family_at_func B WalkingArrow_cat C D
        walking_arrow_tgt)) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)) walking_arrow_tgt)
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @one_cat_cokernel_family_descent_reconstruction B C S C1 t T T0 Q (@zero_arrow_family_incoming_func B C t T A D h)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_zero_family_chain_path B C C1 t T T0 A D h);

// A whole kernel-cokernel pair is fixed-map invertibility of these actual β and γ.
symbol OneCatShortExactFamily [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) : Grpd
≔ @Product_grpd (@OmegaEquivAlong (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S
  C1 t T T0 Q A D h));

// Package the two original whole witnesses; no object isomorphism is substituted.
symbol one_cat_short_exact_family_intro [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  (k : τ (@OmegaEquivAlong (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h))) (q : τ (@OmegaEquivAlong (Functor_cat B C)
    (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h))) : τ (@OneCatShortExactFamily B C S
    C1 t T T0 P Q A D h)
≔ @Product_pair_grpd (@OmegaEquivAlong (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t
  T A D h)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S
  C1 t T T0 Q A D h)) k q;

// Project the original evidence on β:A⇒K(g).
symbol one_cat_short_exact_family_kernel_equiv [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) : τ
    (@OmegaEquivAlong (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
    (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
≔ sigma_Fst R;

// Project the original evidence on γ:Q(f)⇒C.
symbol one_cat_short_exact_family_cokernel_equiv [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) : τ
    (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func
    B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h))
≔ sigma_Snd R;

// Select the supplied whole inverse K(g)⇒A.
symbol one_cat_short_exact_family_kernel_inverse [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P D) A)
≔ @omega_equiv_along_left_inv (Functor_cat B C) A (@kernel_adjunction_family_func B C S t T P D)
  (@kernel_adjunction_family_boundary_transf B C S t T P A D h) (@one_cat_short_exact_family_kernel_equiv B C S C1 t T T0 P Q A
  D h R);

// Select the supplied whole inverse C⇒Q(f), without choosing a section into B.
symbol one_cat_short_exact_family_cokernel_inverse [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h))
  : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)))
≔ @omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) (@zero_arrow_family_incoming_func B C t T A D h)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_row_cokernel_comparison B C S C1 t T T0 Q A D h)
  (@one_cat_short_exact_family_cokernel_equiv B C S C1 t T T0 P Q A D h R);
