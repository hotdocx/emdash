/* Canonical ρ as a whole map; no epicity or inverse is assumed here. */
require open emdash.emdash3_2_one_cat_homology_cover_maps;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D))
  ⊢ (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h) : τ (@Transf B C
    (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P
    Q A D h) b (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)) ≡ (@tapp0_fapp0 (Functor_cat
    WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@cokernel_adjunction_func C S t T0 Q) (@fapp0 B (Functor_cat WalkingArrow_cat C)
    (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b) (@cokernel_adjunction_projection C S t T0
    Q));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (X : τ (Functor B C)) (p : τ (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src)))
  ⊢ (@one_cat_homology_cover_transf B C S C1 t T T0 P Q A D h X p) : τ (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@homology_adjunction_family_func B C S t T T0 P Q A D h));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (X : τ (Functor B C)) (p : τ (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src))) (b : τ (Obj B))
  ⊢ (@tapp0_fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) (@homology_adjunction_family_func B C S t
    T T0 P Q A D h) b (@one_cat_homology_cover_transf B C S C1 t T T0 P Q A D h X p)) ≡ (@comp_fapp0 C (@fapp0 B C
    (@kernel_precomposition_family_func B C S t T P X D p) b) (@fapp0 B C (@kernel_adjunction_family_func B C S t T P
    D) b) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@tapp0_fapp0 B C
    (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h) b
    (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)) (@tapp0_fapp0 B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@kernel_adjunction_family_func B C S t T P D) b
    (@one_cat_kernel_precomposition_second_transf B C S C1 t T T0 P X D p)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (X : τ (Functor B C)) (p : τ (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src))) (b b2 : τ (Obj B))
  ⊢ (@tapp1_func B C (@kernel_precomposition_family_func B C S t T P X D p) (@homology_adjunction_family_func B C S t
    T T0 P Q A D h) b b2 (@one_cat_homology_cover_transf B C S C1 t T T0 P Q A D h X p)) : τ (Functor (Hom_cat B b b2)
    (Hom_cat C (@fapp0 B C (@kernel_precomposition_family_func B C S t T P X D p) b) (@fapp0 B C
    (@homology_adjunction_family_func B C S t T T0 P Q A D h) b2)));

assert [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (Y : τ (Functor B C)) (u v : τ (@Transf B C
    (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y)) (e : τ (@= (@Transf B C
    (@kernel_adjunction_family_func B C S t T P D) Y) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B
    C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y u
    (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h)) (@comp_fapp0 (Functor_cat B C)
    (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y v
    (@homology_adjunction_family_projection_transf B C S t T T0 P Q A D h))))
  ⊢ (@one_cat_homology_projection_reflect_path B C S C1 t T T0 P Q A D h Y u v e) : τ (@= (@Transf B C
    (@homology_adjunction_family_func B C S t T T0 P Q A D h) Y) u v);

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (X : τ (Functor B C)) (p : τ (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src))) (p2 : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
    walking_arrow_src)))
  ⊢ (@one_cat_homology_cover_transf B C S C1 t T T0 P Q A D h X p) : τ (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p2) (@homology_adjunction_family_func B C S t T T0 P Q A D
    h));

assertnot [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) A) D)) (X : τ (Functor B C)) (p : τ (@Transf B C X (@diagram_family_at_func B
    WalkingArrow_cat C D walking_arrow_src))) (Q2 : τ (@CokernelAdjunctionStructure C S t T0))
  ⊢ (@one_cat_homology_cover_transf B C S C1 t T T0 P Q A D h X p) : τ (@Transf B C
    (@kernel_precomposition_family_func B C S t T P X D p) (@homology_adjunction_family_func B C S t T T0 P Q2 A D
    h));
