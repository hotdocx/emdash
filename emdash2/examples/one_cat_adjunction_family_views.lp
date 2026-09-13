/* Whole family comparisons at the existing K/Q formulas and actual factors. */
require open emdash.emdash3_2_one_cat_adjunction_family_views;
require open emdash.emdash3_2_one_cat_image_coimage_factors;

// The complete native result agrees with the existing raw kernel program.
symbol probe_kernel_family_agrees [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  : τ (@= (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) A) D) (Hom_cat (Functor_cat B C) A (@fapp0 _ _ (@comp_cat_cov_func B
    (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
    (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) A D) h) (@kernel_adjunction_family_boundary_transf B C S t T P A D h))
≔ (@one_cat_adjunction_family_transpose_agrees B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P) A D h);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h k : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  ⊢ (@one_cat_adjunction_family_transpose_agrees B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) A D h) : τ (@= (@Transf B C A (@kernel_adjunction_family_func B C S t T P
    D)) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func B C
    (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D) (Hom_cat (Functor_cat B C) A (@fapp0 _
    _ (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
    (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
    WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
    (@kernel_adjunction_evidence C S t T P) A D) h) (@kernel_adjunction_family_boundary_transf B C S t T P A D k));
// The inverse mate recovers the whole original input from that raw formula.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D))
  ⊢ @one_cat_adjunction_family_transpose_reconstruction B C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
    t T P) (@kernel_adjunction_evidence C S t T P) A D h
    : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D) (@fapp0 (Hom_cat (Functor_cat B C) A (@fapp0 _ _ (@comp_cat_cov_func B
      (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D)) (Hom_cat (Functor_cat B (Functor_cat
      WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) A) D) (@one_cat_adjunction_family_untranspose_func B C (Functor_cat
      WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
      (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A D)
      (@kernel_adjunction_family_boundary_transf B C S t T P A D h)) h);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (b : τ (Obj B))
  ⊢ @eq_ap (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)) (Hom C (@fapp0 B C A b) (@fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) b)) (λ eta : τ (@Transf B C A (@kernel_adjunction_family_func B C S t
    T P D)), @tapp0_fapp0 B C A (@kernel_adjunction_family_func B C S t T P D) b eta)
      (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D) (Hom_cat (Functor_cat B C) A (@fapp0 _ _
        (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
        (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P) A D) h) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
        (@one_cat_adjunction_family_transpose_agrees B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P) A D h)
    : τ (@= (Hom C (@fapp0 B C A b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) b)) (@tapp0_fapp0 B C A
      (@kernel_adjunction_family_func B C S t T P D) b (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C))
      (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D)
      (Hom_cat (Functor_cat B C) A (@fapp0 _ _ (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P)) D)) (@one_cat_adjunction_family_transpose_func B C (Functor_cat
      WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
      (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) A D) h)) (@tapp0_fapp0 B C A
      (@kernel_adjunction_family_func B C S t T P D) b (@kernel_adjunction_family_boundary_transf B C S t T P A D h)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (b c : τ (Obj B))
  ⊢ @eq_ap (@Transf B C A (@kernel_adjunction_family_func B C S t T P D)) (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B
    C A b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) c))) (λ eta : τ (@Transf B C A
    (@kernel_adjunction_family_func B C S t T P D)), @tapp1_func B C A (@kernel_adjunction_family_func B C S t T P D) b
    c eta)
      (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) A) D) (Hom_cat (Functor_cat B C) A (@fapp0 _ _
        (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
        (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P) A D) h) (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
        (@one_cat_adjunction_family_transpose_agrees B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
        WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P) A D h)
    : τ (@= (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C A b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P
      D) c))) (@tapp1_func B C A (@kernel_adjunction_family_func B C S t T P D) b c (@fapp0 (Hom_cat (Functor_cat B
      (Functor_cat WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) A) D) (Hom_cat (Functor_cat B C) A (@fapp0 _ _ (@comp_cat_cov_func B
      (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D))
      (@one_cat_adjunction_family_transpose_func B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
      WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P) A D) h)) (@tapp1_func B C A (@kernel_adjunction_family_func B C S t T P D)
      b c (@kernel_adjunction_family_boundary_transf B C S t T P A D h)));
// The complete native result agrees with the existing raw cokernel program.
symbol probe_cokernel_family_agrees [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T) A)))
  : τ (@= (@Transf B C (@cokernel_adjunction_family_func B C S t T Q D) A) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) D (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T)) A)) (Hom_cat (Functor_cat B C) (@fapp0 _ _ (@comp_cat_cov_func B (Functor_cat
    WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)) D) A) (@one_cat_adjunction_family_untranspose_func B
    (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C
    S t T Q) (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T Q) D A) h)
    (@cokernel_adjunction_family_colift_transf B C S t T Q D A h))
≔ (@one_cat_adjunction_family_untranspose_agrees B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
  WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
  (@cokernel_adjunction_evidence C S t T Q) D A h);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h k : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T) A)))
  ⊢ (@one_cat_adjunction_family_untranspose_agrees B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
    WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
    (@cokernel_adjunction_evidence C S t T Q) D A h) : τ (@= (@Transf B C (@cokernel_adjunction_family_func B C S t T Q
    D) A) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 _ _ (@comp_cat_cov_func B C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A)) (Hom_cat (Functor_cat B C) (@fapp0 _ _
    (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)) D) A)
    (@one_cat_adjunction_family_untranspose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
    WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
    (@cokernel_adjunction_evidence C S t T Q) D A) h) (@cokernel_adjunction_family_colift_transf B C S t T Q D A k));
// The inverse mate recovers the whole original input from that raw formula.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  ⊢ @one_cat_adjunction_family_untranspose_reconstruction B (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q)
    (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T Q) D A h
    : τ (@= (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T) A)) (@fapp0 (Hom_cat (Functor_cat B C) (@fapp0 _ _ (@comp_cat_cov_func B
      (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)) D) A) (Hom_cat (Functor_cat B
      (Functor_cat WalkingArrow_cat C)) D (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T)) A)) (@one_cat_adjunction_family_transpose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q)
      (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T Q) D A)
      (@cokernel_adjunction_family_colift_transf B C S t T Q D A h)) h);
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
    (b : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@cokernel_adjunction_family_func B C S t T Q D) A) (Hom C (@fapp0 B C
    (@cokernel_adjunction_family_func B C S t T Q D) b) (@fapp0 B C A b)) (λ eta : τ (@Transf B C
    (@cokernel_adjunction_family_func B C S t T Q D) A), @tapp0_fapp0 B C (@cokernel_adjunction_family_func B C S t T Q
    D) A b eta)
      (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 _ _ (@comp_cat_cov_func B C
        (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A)) (Hom_cat (Functor_cat B C) (@fapp0 _ _
        (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)) D) A)
        (@one_cat_adjunction_family_untranspose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
        WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
        (@cokernel_adjunction_evidence C S t T Q) D A) h) (@cokernel_adjunction_family_colift_transf B C S t T Q D A h)
        (@one_cat_adjunction_family_untranspose_agrees B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
        WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
        (@cokernel_adjunction_evidence C S t T Q) D A h)
    : τ (@= (Hom C (@fapp0 B C (@cokernel_adjunction_family_func B C S t T Q D) b) (@fapp0 B C A b)) (@tapp0_fapp0 B C
      (@cokernel_adjunction_family_func B C S t T Q D) A b (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat
      C)) D (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T))
      A)) (Hom_cat (Functor_cat B C) (@fapp0 _ _ (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T Q)) D) A) (@one_cat_adjunction_family_untranspose_func B (Functor_cat
      WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q)
      (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T Q) D A) h)) (@tapp0_fapp0 B C
      (@cokernel_adjunction_family_func B C S t T Q D) A b (@cokernel_adjunction_family_colift_transf B C S t T Q D A
      h)));
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
    (b c : τ (Obj B))
  ⊢ @eq_ap (@Transf B C (@cokernel_adjunction_family_func B C S t T Q D) A) (Functor (Hom_cat B b c) (Hom_cat C (@fapp0
    B C (@cokernel_adjunction_family_func B C S t T Q D) b) (@fapp0 B C A c))) (λ eta : τ (@Transf B C
    (@cokernel_adjunction_family_func B C S t T Q D) A), @tapp1_func B C (@cokernel_adjunction_family_func B C S t T Q
    D) A b c eta)
      (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) D (@fapp0 _ _ (@comp_cat_cov_func B C
        (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T)) A)) (Hom_cat (Functor_cat B C) (@fapp0 _ _
        (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)) D) A)
        (@one_cat_adjunction_family_untranspose_func B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
        WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
        (@cokernel_adjunction_evidence C S t T Q) D A) h) (@cokernel_adjunction_family_colift_transf B C S t T Q D A h)
        (@one_cat_adjunction_family_untranspose_agrees B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category
        WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
        (@cokernel_adjunction_evidence C S t T Q) D A h)
    : τ (@= (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@cokernel_adjunction_family_func B C S t T Q D) b) (@fapp0
      B C A c))) (@tapp1_func B C (@cokernel_adjunction_family_func B C S t T Q D) A b c (@fapp0 (Hom_cat (Functor_cat B
      (Functor_cat WalkingArrow_cat C)) D (@fapp0 _ _ (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
      (@initial_arrow_diagram_func C t T)) A)) (Hom_cat (Functor_cat B C) (@fapp0 _ _ (@comp_cat_cov_func B (Functor_cat
      WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)) D) A) (@one_cat_adjunction_family_untranspose_func B
      (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func
      C S t T Q) (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T Q) D A) h)) (@tapp1_func B C
      (@cokernel_adjunction_family_func B C S t T Q D) A b c (@cokernel_adjunction_family_colift_transf B C S t T Q D A
      h)));

// The published whole image factor is the same mate at the actual input.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @one_cat_adjunction_family_transpose_agrees (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
    t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@cokernel_adjunction_arrow_func C S t T0 Q) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q)
    : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src) (@adjunction_image_func C S t T T0 P Q))
      (@fapp0 (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@fapp0 _ _
        (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
        (@cokernel_adjunction_arrow_func C S t T0 Q)) (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) C)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat
        WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
        (@cokernel_adjunction_arrow_func C S t T0 Q))) (@one_cat_adjunction_family_transpose_func (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
        (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q));

// The published raw factor reconstructs the entire original input by inverse mating.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @one_cat_adjunction_family_transpose_reconstruction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat
    C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
    (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)
    (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q)
    : τ (@= (Obj (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@fapp0 _ _
      (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
      (@cokernel_adjunction_arrow_func C S t T0 Q))) (@fapp0 (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat
      WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@cokernel_adjunction_arrow_func C S t T0 Q))) (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
      WalkingArrow_cat C)) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat
      WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_family_untranspose_func
      (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat
      C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t
      T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0
      Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q));

// The published whole coimage factor is the same mate at the actual input.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @one_cat_adjunction_family_untranspose_agrees (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@one_cat_kernel_counit_mate_input C S C1 t
    T T0 P)
    : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
      (@fapp0 (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
        (@kernel_adjunction_arrow_func C S t T P) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
        (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_tgt))) (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@fapp0 _ _
        (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
        (@cokernel_adjunction_func C S t T0 Q)) (@kernel_adjunction_arrow_func C S t T P)) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_family_untranspose_func (Functor_cat
        WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
        (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
        T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input C S C1 t T T0 P)) (@one_cat_adjunction_coimage_to_target
        C S C1 t T T0 P Q));

// The published raw factor reconstructs the entire original input by inverse mating.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ @one_cat_adjunction_family_untranspose_reconstruction (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat
    C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
    (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
    T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@one_cat_kernel_counit_mate_input C S C1 t
    T T0 P)
    : τ (@= (Obj (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
      (@kernel_adjunction_arrow_func C S t T P) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
      (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)) (@diagram_evaluation_at_func
      WalkingArrow_cat C walking_arrow_tgt)))) (@fapp0 (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@fapp0
      _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T0 Q)) (@kernel_adjunction_arrow_func C S t T P)) (@diagram_evaluation_at_func
      WalkingArrow_cat C walking_arrow_tgt)) (Hom_cat (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
      WalkingArrow_cat C)) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat
      WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0))
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))) (@one_cat_adjunction_family_transpose_func
      (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C
      C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence
      C S t T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
      walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@one_cat_kernel_counit_mate_input
      C S C1 t T T0 P));

// Existing associativity of whole transformations remains available.
assert (B C : Cat) (A D E H : τ (Functor B C))
  (f : τ (@Transf B C A D)) (g : τ (@Transf B C D E)) (h : τ (@Transf B C E H))
  ⊢ eq_refl (@comp_fapp0 (Functor_cat B C) A E H h (@comp_fapp0 (Functor_cat B C) A D E g f))
    : τ (@= (@Transf B C A H)
      (@comp_fapp0 (Functor_cat B C) A E H h (@comp_fapp0 (Functor_cat B C) A D E g f))
      (@comp_fapp0 (Functor_cat B C) A D H (@comp_fapp0 (Functor_cat B C) D E H h g) f));

// Mixed represented/raw associativity is proof-time, with all original operands.
assert (B C L R : Cat) (A : τ (Functor B C)) (F : τ (Functor C L)) (G : τ (Functor L R))
  ⊢ eq_refl (@comp_cat_fapp0 B L R G
      (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B C L F A))
    : τ (@= (Functor B R)
      (@comp_cat_fapp0 B L R G (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B C L F A))
      (@comp_cat_fapp0 B C R (@comp_cat_fapp0 C L R G F) A));
assertnot (B C L R : Cat) (A A' : τ (Functor B C)) (F : τ (Functor C L)) (G : τ (Functor L R))
  ⊢ eq_refl (@comp_cat_fapp0 B L R G
      (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B C L F A))
    : τ (@= (Functor B R)
      (@comp_cat_fapp0 B L R G (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B C L F A))
      (@comp_cat_fapp0 B C R (@comp_cat_fapp0 C L R G F) A'));
assertnot (B C L R : Cat) (A : τ (Functor B C)) (F : τ (Functor C L)) (G : τ (Functor L R))
  ⊢ @comp_cat_fapp0 B L R G (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B C L F A)
    ≡ @comp_cat_fapp0 B C R (@comp_cat_fapp0 C L R G F) A;
