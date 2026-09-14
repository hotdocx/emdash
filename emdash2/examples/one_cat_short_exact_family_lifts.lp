/* Whole native row lift, original input recovery and retained Hom action. */
require open emdash.emdash3_2_one_cat_short_exact_family_lifts;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C))
  ⊢ (@one_cat_short_exact_family_lift_func B C S C1 t T T0 P Q A D h R X) : τ (Functor (Hom_cat (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat
    (Functor_cat B C) X A));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))))
  ⊢ (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z) ≡ (@hom_postcomp_fapp0 (Functor_cat B C)
    (Functor_cat B C) (@id_func (Functor_cat B C)) X (@kernel_adjunction_family_func B C S t T P D) A
    (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A D h R) (@one_cat_kernel_family_lift B C S C1 t T
    T0 P X D k z));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))))
  ⊢ (@one_cat_short_exact_family_lift_path B C S C1 t T T0 P Q A D h R X k z) : τ (@= (@Transf B C X A)
    (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z) (@comp_fapp0 (Functor_cat B C) X
    (@kernel_adjunction_family_func B C S t T P D) A (@one_cat_short_exact_family_kernel_inverse B C S C1 t T T0 P Q A
    D h R) (@one_cat_kernel_family_lift B C S C1 t T T0 P X D k z)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt))))
  ⊢ (@one_cat_short_exact_family_lift_reconstruction B C S C1 t T T0 P Q A D h R X k z) : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X A
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T A D
    h) (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z)) k);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (v w : τ (Obj (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) X) D)))
  ⊢ (@fapp1_func (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X A) (@one_cat_short_exact_family_lift_func
    B C S C1 t T T0 P Q A D h R X) v w) : τ (Functor (Hom_cat (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat
    C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
    (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D) v w) (Hom_cat (Hom_cat (Functor_cat B
    C) X A) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X A) (@one_cat_short_exact_family_lift_func
    B C S C1 t T T0 P Q A D h R X) v) (@fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0
    (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
    WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X A)
    (@one_cat_short_exact_family_lift_func B C S C1 t T T0 P Q A D h R X) w)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (v w : τ (Obj (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) X) D))) (alpha : τ (Hom (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C)
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X) D) v w))
  ⊢ (@fapp1_fapp0 (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat (Functor_cat B C) X A) (@one_cat_short_exact_family_lift_func
    B C S C1 t T T0 P Q A D h R X) v w alpha) : τ (Hom (Hom_cat (Functor_cat B C) X A) (@fapp0 (Hom_cat (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
    (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D) (Hom_cat
    (Functor_cat B C) X A) (@one_cat_short_exact_family_lift_func B C S C1 t T T0 P Q A D h R X) v) (@fapp0 (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) X) D) (Hom_cat (Functor_cat B C) X A) (@one_cat_short_exact_family_lift_func B C S C1 t T T0 P Q A D h R X)
    w));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (k : τ (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (z : τ (@= (@Transf B C X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
    (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) k) (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_tgt)))) (k2 : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src))) (z2 : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B
    WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) k2)
    (@zero_arrow_family_zero_transf B C t T T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))))
  ⊢ (@one_cat_short_exact_family_lift B C S C1 t T T0 P Q A D h R X k z) ≡ (@one_cat_short_exact_family_lift B C S C1
    t T T0 P Q A D h R X k2 z2);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
    WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    D)) (R : τ (@OneCatShortExactFamily B C S C1 t T T0 P Q A D h)) (X : τ (Functor B C)) (v w : τ (Obj (Hom_cat
    (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat
    WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
    T)) X) D)))
  ⊢ (@eq_refl (Obj (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@fapp0 (Functor_cat B C) (Functor_cat B
    (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T)) X) D)) v) : τ (@= (Obj (Hom_cat (Functor_cat B (Functor_cat WalkingArrow_cat
    C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C
    (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) X) D)) v w);
