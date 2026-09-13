/* Independent whole H: actual boundary, diagram action and higher views. */
require open emdash.emdash3_2_homology_adjunction_families;


// The introduced diagram retains its whole endpoint functor.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) ⊢
  @diagram_family_at_func B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) walking_arrow_src
  ≡ A;


// The introduced diagram retains its whole endpoint functor.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) ⊢
  @diagram_family_at_func B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) walking_arrow_tgt
  ≡ (@kernel_adjunction_family_func B C S t T P D);


// Its whole generator is the original boundary transformation.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) ⊢
  @diagram_family_transf B WalkingArrow_cat C (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h)
    walking_arrow_src walking_arrow_tgt walking_arrow_generator
  ≡ (@kernel_adjunction_family_boundary_transf B C S t T P A D h);


// The component computes to K(h_b) ∘ η_A[b].
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B)) ⊢
  @tapp0_fapp0 B C A (@kernel_adjunction_family_func B C S t T P D) b (@kernel_adjunction_family_boundary_transf B C S t T P A D h)
  ≡ @comp_fapp0 C _ _ _
    (@fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@fapp0 B C A b))
      (@fapp0 B (Functor_cat WalkingArrow_cat C) D b) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C)
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D b h))
    (@tapp0_fapp0 C C (@id_func C)
      (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@terminal_arrow_diagram_func C t T))
      (@fapp0 B C A b)
      (@unit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
        (@kernel_adjunction_evidence C S t T P)));


// Nonidentity boundary-diagram action retains the actual endpoint map.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C
    (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b)
    (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) c) walking_arrow_src
    (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b c p)
  ≡ @fapp1_fapp0 B C A b c p;


// Nonidentity boundary-diagram action retains the actual endpoint map.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @tapp0_fapp0 WalkingArrow_cat C
    (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b)
    (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) c) walking_arrow_tgt
    (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b c p)
  ≡ @fapp1_fapp0 B C (@kernel_adjunction_family_func B C S t T P D) b c p;


// H acts through the original whole Q on that boundary-diagram map.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c p
  ≡ @fapp1_fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
    (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b)
    (@fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) c)
    (@fapp1_fapp0 B (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P A D h) b c p);


// Generic composition remains the existing functor cut.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (a b c : τ (Obj B)) (p : τ (Hom B a b)) (q : τ (Hom B b c)) ⊢
  @comp_fapp0 C _ _ _
    (@fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c q) (@fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) a b p)
  ≡ @fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) a c (@comp_fapp0 B a b c q p);


// A further Hom level is retained and has the generic identity computation.
assert [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c)) ⊢
  @fapp1_fapp0 _ _ (@fapp1_func B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c) p p (@id (Hom_cat B b c) p)
  ≡ @id (Hom_cat C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) c))
    (@fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c p);


// An unrelated arrow of the same type is not the result.
assertnot [B C : Cat] (S : τ (@PreadditiveCategory C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
      (@terminal_arrow_diagram_func C t T) A) D)) (b c : τ (Obj B)) (p : τ (Hom B b c))
  (other : τ (Hom C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) c))) ⊢
  @eq_refl (Hom C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) c))
    (@fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c p)
  : τ (@= (Hom C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) c))
      (@fapp1_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b c p) other);
