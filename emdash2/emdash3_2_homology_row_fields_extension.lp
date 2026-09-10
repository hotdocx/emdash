/* Literal row/map-indexed step, preserving the same original H applications. */
require open emdash.emdash3_2_homology_row_triples;
require open emdash.emdash3_2_homology_window_extension;

symbol homology_row_fields_extend [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (R0 R1 R2 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T R0) (@short_exact_row_family_func I C C1 P t
    (@computational_abelian_preabelian C P t Ab) T R1))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)
    (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2)))
  (z0 : τ (@RowFamilyMiddleChainZero I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 R2 f g))
  (R3 : τ (@ShortExactRowFamily I C C1 P t (@computational_abelian_preabelian C P t Ab) T)) (h : τ (@Transf I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
    R2) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3)))
  (z1 : τ (@RowFamilyMiddleChainZero I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 R3 g h))
  (x : τ (Obj I)) (n : τ Nat_grpd) (rest : τ (@ComputationalExactArrowTail C P t (@computational_abelian_preabelian C P
    t Ab) n (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
    Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) (@short_exact_row_chain_source_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
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
     R2) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 R3 h x) (z1 x))))
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
     (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
     (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
     Ab)) KP QP)
   (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
     (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@short_exact_row_chain_middle_pair C P t
     (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t
     T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian
     C P t Ab) T R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
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
     R2) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 R3 h x) (z1 x))))
     (@chain_pair_homology_action C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
     Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
     t (@computational_abelian_preabelian C P t Ab)) KP QP (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0 (@ZeroArrowCone_cat C t T) C
     (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t
     T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src)
     (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) walking_arrow_src) (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab)
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
     R2) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 R3 h x) (z1 x))
     (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
     C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 R3 h x) (z1 x))
     (@short_exact_row_chain_inclusion C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
     t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C
     C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
     WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_tgt)
     (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
     (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2) x)) (@fapp0
     WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R2) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
     (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
     (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
     (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
     (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T
     R3) x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1
     x) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
     (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3 x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x)
     (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 R3 h x) (z1 x)))))
  : τ (@ComputationalExactArrowTail C P t (@computational_abelian_preabelian C P t Ab) (succ (succ (succ n))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
    Ab)) KP QP)
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
≔ @homology_whole_window_extend C P t Ab (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t
  Ab) T R0) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T R0) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0)
  x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)
  x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T R1) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1)
  x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2)
  x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T R2) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2)
  x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3)
  x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t
  (@computational_abelian_preabelian C P t Ab) T R3) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3)
  x)) walking_arrow_tgt) (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 x)
  (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 x)
  (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 x)
  (@short_exact_row_family_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R3 x)
  (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R0 R1 f x)
  (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R1 R2 g x)
  (@short_exact_row_family_transf_at I C C1 P t (@computational_abelian_preabelian C P t Ab) T R2 R3 h x) (z0 x) (z1 x)
  C1 T T0 KP QP n rest;
