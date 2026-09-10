/* The final window interior at the actual whole H objects and arrows. */
require open emdash.emdash3_2_homology_third_exactness;

// The universal family covers every test killed by the actual H(i').
assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)))) ⊢
  @homology_whole_window_third_covers C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP
  : τ (@HasComputationalExactCovers C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t
    T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP));

// Exactness is the existing predicate at the unchanged third pair.
assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)))) ⊢
  @homology_whole_window_third_exact C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero C1 T T0 KP QP
  : τ (@ComputationalExactAt C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0
    B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP) (@computational_homology_at C P t (@computational_abelian_preabelian C P t
    Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C
    P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP)));

// Its content is epicity of the actual selected boundary, not of delta.
assert [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)))) ⊢
  @homology_whole_window_third_exact C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero C1 T T0 KP QP
  : τ (@IsEpic C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
    (@computational_homology_cycle_object C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
      (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
      t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
      B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
      (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2
      D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP) (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
      (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
      (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
      t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
      B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
      (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2
      D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP)))
    (@computational_homology_boundary C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
      t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
      (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
      t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
      B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
      (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2
      D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP) (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
      (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
      (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
      (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
      (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P
      t (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0
      B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
      C P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))
      (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T
      (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2
      (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2
      D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2
      D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP))));

assertnot [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 : τ (Obj C)]
  (rowm : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm))
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (row2 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2))
  (F : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
    row0)))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A0 B0 D0 row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
    row1)))
  (J : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) A1 B1 D1 A2 B2 D2 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
    A1 B1 D1 row1) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2
    row2)))
  (upper_zero : τ (@= (Hom C Bm B1) (@comp_fapp0 C Bm B0 B1 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) Bm B1)))
  (lower_zero : τ (@= (Hom C B0 B2) (@comp_fapp0 C B0 B1 B2 (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 A2 B2 D2
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A2 B2 D2 row2) J)
    (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B0 B2)))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (KP : τ (@KernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab))))
  (QP : τ (@CokernelPresentation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)))) ⊢
  @homology_whole_window_third_exact C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero C1 T T0 KP QP
  : τ (@IsEpic C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@homology_record_connecting C P t Ab Am Bm Dm A0 B0 D0 A1
    B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero (@chain_pair_homology_record C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0
    D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))
    (@chain_pair_homology_record C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
    t (@computational_abelian_preabelian C P t Ab)) KP QP A0 A1 A2 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))));
