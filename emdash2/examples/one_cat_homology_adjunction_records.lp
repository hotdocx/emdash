/* Ordinary record views keep the original whole operations and action.
   No selected W/V families or per-map coherence premises appear. */
require open emdash.emdash3_2_one_cat_homology_adjunction_records;

// Cycles retain the whole K observation.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B)) ⊢
  (@homology_record_cycle_object C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h b))
  ≡ @fapp0 B C (@kernel_adjunction_family_func B C S t T P D) b;

// The boundary is the actual whole β, not a newly selected test lift.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B)) ⊢
  (@homology_record_boundary C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h b))
  ≡ @tapp0_fapp0 B C A (@kernel_adjunction_family_func B C S t T P D) b (@kernel_adjunction_family_boundary_transf B C S t T P A D h);

// Homology is literally the existing whole H at this input.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B)) ⊢
  (@homology_record_object C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h b))
  ≡ @fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b;

// Its projection observes Q at the actual whole boundary diagram.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b : τ (Obj B)) ⊢
  (@homology_record_projection C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h b))
  ≡ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _
      (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b)
      (@cokernel_adjunction_projection C S t T0 Q);

// An arbitrary base arrow acts through the original whole H at record endpoints.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b c : τ (Obj B)) (g : τ (Hom B b c)) ⊢
  @fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c g
  : τ (Hom C (@homology_record_object C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h b))
      (@homology_record_object C S (@fapp0 B C A c) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D c) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D c) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h c) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h c)));

// The whole Hom action remains available at the same endpoints.
assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D))
  (b c : τ (Obj B)) ⊢
  @fapp1_func B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c
  : τ (Functor (Hom_cat B b c)
      (Hom_cat C (@homology_record_object C S (@fapp0 B C A b) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h b) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h b))
      (@homology_record_object C S (@fapp0 B C A c) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D c) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D c) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h c) (@homology_adjunction_family_record B C S C1 t T T0 P Q A D h c))));
