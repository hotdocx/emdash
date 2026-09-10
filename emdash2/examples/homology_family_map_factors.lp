/* Literal record observations and the next Hom action of the whole projection. */
require open emdash.emdash3_2_homology_family_map_factors;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj B)) ⊢
  (@homology_record_cycle_embedding C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) ≡ @tapp0_fapp0 B C
    (@kernel_family_func B C S t T W P D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src) D) x (@kernel_family_inclusion_transf B C S t T W P D);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) (x : τ (Obj B)) ⊢
  (@homology_record_projection C S (@fapp0 B C A x) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 B (Functor_cat WalkingArrow_cat C) D x) walking_arrow_tgt)
    (@homology_family_pair B C S t T A D h x) (@homology_family_record B C S t T T0 W V P Q A D h x)) ≡ @tapp0_fapp0 B C
    (@kernel_family_func B C S t T W P D) (@homology_family_func B C S t T T0 W V P Q A D h) x (@homology_family_projection_transf B
    C S t T T0 W V P Q A D h);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) [x y : τ (Obj B)] (p q : τ
      (Hom B x y)) ⊢
  @fapp1_func (Hom_cat B x y) (Hom_cat C (@fapp0 B C (@kernel_family_func B C S t T W P D) x) (@fapp0 B C (@homology_family_func B C
    S t T T0 W V P Q A D h) y))
    (@tapp1_func B C (@kernel_family_func B C S t T W P D) (@homology_family_func B C S t T T0 W V P Q A D h) x y
      (@homology_family_projection_transf B C S t T T0 W V P Q A D h)) p q
  : τ (Functor (Hom_cat (Hom_cat B x y) p q)
      (Hom_cat (Hom_cat C (@fapp0 B C (@kernel_family_func B C S t T W P D) x) (@fapp0 B C (@homology_family_func B C S t T T0 W V P
        Q A D h) y)) (@tapp1_fapp0 B C (@kernel_family_func B C S t T W P D) (@homology_family_func B C S t T T0 W V P Q A D h) x y
        (@homology_family_projection_transf B C S t T T0 W V P Q A D h) p) (@tapp1_fapp0 B C (@kernel_family_func B C S t T W P D)
        (@homology_family_func B C S t T T0 W V P Q A D h) x y (@homology_family_projection_transf B C S t T T0 W V P Q A D h) q)));
