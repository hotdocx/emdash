/* Implementation entry over directly indexed whole row data.
   The existing packed-state facade remains separate research: converting its
   expanded H(inclusion) index against this entry currently exceeds the LF bound.
   This module assembles every finite number of windows; endpoint clipping/zeros
   and the final public bounded-result interface remain downstream. */
/* Nat assembly over directly retained row/map indices; no new H or exactness choice. */
require open emdash.emdash3_2_homology_row_field_span_case;
require open emdash.emdash3_2_homology_row_fields_extension;

symbol homology_row_field_span_exact_length (n : τ Nat_grpd) : τ Nat_grpd
≔ @nat_elim (λ _ : τ Nat_grpd, Nat_grpd) zero
    (λ _ : τ Nat_grpd, λ m : τ Nat_grpd, succ (succ (succ m))) n;

symbol homology_row_field_span_exact_tail [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (n : τ Nat_grpd) (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T R0) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g))
  (span : τ (@HomologyRowFieldSpan I C C1 P t (@computational_abelian_preabelian C P t Ab) T n R0 R1 R2 f g z0)) (x : τ
    (Obj I))
  : τ (@ComputationalExactArrowTail C P t (@computational_abelian_preabelian C P t Ab)
    (@homology_row_field_span_exact_length n) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@short_exact_row_chain_source_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
     (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
     (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
     Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@short_exact_row_chain_middle_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
     Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
     t (@computational_abelian_preabelian C P t Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t
     T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_src) (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
     C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
     t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd, @Pi_grpd (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T) (λ R0
      : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T), @Pi_grpd
      (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T) (λ R1 : τ (@ShortExactRowFamily I
      C C1 P t (@computational_abelian_preabelian C P t Ab) T), @Pi_grpd (@ShortExactRowFamily I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T) (λ R2 : τ (@ShortExactRowFamily I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T), @Pi_grpd (@Transf I (@ZeroArrowCone_cat C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)) (λ f : τ (@Transf I
      (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      R0) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)), @Pi_grpd
      (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
      C P t Ab) T R1) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2)) (λ g
      : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R1) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R2)), @Pi_grpd (@RowFamilyMiddleChainZero I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g) (λ z0 : τ (@RowFamilyMiddleChainZero I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g), @Pi_grpd (@HomologyRowFieldSpan I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T n0 R0 R1 R2 f g z0) (λ span : τ (@HomologyRowFieldSpan I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T n0 R0 R1 R2 f g z0), @Pi_grpd (Obj I) (λ x : τ (Obj I),
      (@ComputationalExactArrowTail C P t (@computational_abelian_preabelian C P t Ab)
      (@homology_row_field_span_exact_length n0) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@short_exact_row_chain_source_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
     (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
     (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
     Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@short_exact_row_chain_middle_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
     Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
     t (@computational_abelian_preabelian C P t Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t
     T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_src) (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
     C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
     t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0
     x)))))))))))))
    (λ R0 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T),
      λ R1 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T),
      λ R2 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T),
      λ f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R0) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R1)),
      λ g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R1) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R2)),
      λ z0 : τ (@RowFamilyMiddleChainZero I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g),
      λ span : τ (@HomologyRowFieldSpan I C C1 P t (@computational_abelian_preabelian C P t Ab) T zero R0 R1 R2 f g z0),
      λ x : τ (Obj I),
      @computational_exact_arrow_tail_nil C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
        C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
        (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
        P t Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@short_exact_row_chain_source_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
     (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
     (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
     Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@short_exact_row_chain_middle_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
     Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
     t (@computational_abelian_preabelian C P t Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t
     T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_src) (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
     C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
     t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
    (λ n0 : τ Nat_grpd, λ rec : τ (@Pi_grpd (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t
      Ab) T) (λ R0 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T), @Pi_grpd
      (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T) (λ R1 : τ (@ShortExactRowFamily I
      C C1 P t (@computational_abelian_preabelian C P t Ab) T), @Pi_grpd (@ShortExactRowFamily I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T) (λ R2 : τ (@ShortExactRowFamily I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T), @Pi_grpd (@Transf I (@ZeroArrowCone_cat C t T)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0)
      (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)) (λ f : τ (@Transf I
      (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
      R0) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)), @Pi_grpd
      (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
      C P t Ab) T R1) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2)) (λ g
      : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R1) (@short_exact_row_family_func I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R2)), @Pi_grpd (@RowFamilyMiddleChainZero I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g) (λ z0 : τ (@RowFamilyMiddleChainZero I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g), @Pi_grpd (@HomologyRowFieldSpan I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T n0 R0 R1 R2 f g z0) (λ span : τ (@HomologyRowFieldSpan I C C1 P t
      (@computational_abelian_preabelian C P t Ab) T n0 R0 R1 R2 f g z0), @Pi_grpd (Obj I) (λ x : τ (Obj I),
      (@ComputationalExactArrowTail C P t (@computational_abelian_preabelian C P t Ab)
      (@homology_row_field_span_exact_length n0) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
      (@computational_abelian_preabelian C P t Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@short_exact_row_chain_source_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
     (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
     (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
     Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@short_exact_row_chain_middle_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
     Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
     t (@computational_abelian_preabelian C P t Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t
     T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_src) (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
     C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
     t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0
     x))))))))))))),
      λ R0 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T),
      λ R1 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T),
      λ R2 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T),
      λ f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R0) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R1)),
      λ g : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R1) (@short_exact_row_family_func I C C1 P t
        (@computational_abelian_preabelian C P t Ab) T R2)),
      λ z0 : τ (@RowFamilyMiddleChainZero I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g),
      λ span : τ (@HomologyRowFieldSpan I C C1 P t (@computational_abelian_preabelian C P t Ab) T (succ n0) R0 R1 R2 f g
        z0),
      λ x : τ (Obj I),
      @homology_row_field_span_case I C C1 P t (@computational_abelian_preabelian C P t Ab) T n0 R0 R1 R2 f g z0 (@ComputationalExactArrowTail C P t (@computational_abelian_preabelian C P t Ab)
    (succ (succ (succ (@homology_row_field_span_exact_length n0)))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@short_exact_row_chain_source_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
     (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
     (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
     Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@short_exact_row_chain_middle_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
     (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
     Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
     t (@computational_abelian_preabelian C P t Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t
     T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_src) (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
     C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))
     (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
     t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x) (z0 x))))
        (λ R3 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T), λ h : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3)), λ z1 : τ (@RowFamilyMiddleChainZero I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 R3 g h),
          λ rest : τ (@HomologyRowFieldSpan I C C1 P t (@computational_abelian_preabelian C P t Ab) T n0 R1 R2 R3 g h z1),
          @homology_row_fields_extend I C C1 P t Ab T T0 KP QP
            R0 R1 R2 f g z0 R3 h z1 x (@homology_row_field_span_exact_length n0)
            (rec R1 R2 R3 g h z1 rest x))
        span)
    n) R0 R1 R2 f g z0 span x;
