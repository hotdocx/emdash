/* Ordinary records of the existing whole H = Q ∘ Arr(K(h) ∘ η).
   Whole adjunctions supply universality. The boundary field retains the
   actual h, and the quotient observes its whole introduced diagram family.
   These are record views; no H, coherence field or computation rule is added. */
require open emdash.emdash3_2_homology_records;
require open emdash.emdash3_2_homology_adjunction_record_data;
require open emdash.emdash3_2_one_cat_adjunction_records;
require open emdash.emdash3_2_homology_adjunction_families;

// Ordinary record retaining the actual whole boundary.
symbol homology_adjunction_family_record [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B))
  : τ (@HomologyRecord C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
      (@homology_family_pair B C S t T A D h b))
≔ @homology_record_intro C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b)
    (@kernel_adjunction_record C S C1 t T P (@fapp0 B (Functor_cat WalkingArrow_cat C) D b))
    (@kernel_adjunction_semantic_boundary_factor C S t T P (@fapp0 B C A b) (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D b h))
    (@cokernel_adjunction_record C S C1 t T0 Q
      (@fapp0 B (Functor_cat WalkingArrow_cat C)
        (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b));
