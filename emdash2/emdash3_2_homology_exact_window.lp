/*
  Exactness data indexed by the original whole-H window.
  The three existing pairs own all objects, arrows and adjacent-zero paths.
  This transparent product stores only their three exactness witnesses.
*/
require open emdash.emdash3_2_homology_window;

// The existing groupoidal product is the constant-fibre Sigma package.
symbol HomologyWholeExactWindow [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab)))) : Grpd
≔ (@Product_grpd (@computational_exact_at_selected C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
  Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero C1 T T0 KP QP)) (@Product_grpd (@computational_exact_at_selected C P t (@computational_abelian_preabelian
  C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
  Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero))) (@homology_whole_window_second_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP)) (@computational_exact_at_selected C P t
  (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
  D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero C1 T T0 KP QP))));

symbol homology_whole_exact_window_intro [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (e0 : τ (@computational_exact_at_selected C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Am A0 A1 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
    Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
    (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
    (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP))) (e1 : τ (@computational_exact_at_selected C P t
    (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
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
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_second_pair C P t Ab Am Bm Dm A0 B0
    D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP))) (e2 : τ
    (@computational_exact_at_selected C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C
    t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
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
    upper_zero lower_zero C1 T T0 KP QP)))
  : τ (@HomologyWholeExactWindow C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
    lower_zero C1 T T0 KP QP)
≔ @Product_pair_grpd (@computational_exact_at_selected C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1
  rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
  Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
  (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero C1 T T0 KP QP)) (@Product_grpd (@computational_exact_at_selected C P t (@computational_abelian_preabelian
  C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
  Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
  (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t
  Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
  P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) KP A0 A1 A2
  (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2
  row0 row1 row2 G J lower_zero))) (@homology_whole_window_second_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP)) (@computational_exact_at_selected C P t
  (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
  C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab)
  Am Bm Dm rowm) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
  row0) F) (@short_exact_row_chain_target_zero_path C P t (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0
  D0 A1 B1 D1 rowm row0 row1 F G upper_zero)))) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
  (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C
  P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
  C P t Ab)) KP A0 A1 A2 (@short_exact_row_chain_source_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0
  D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
  t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P
  t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
  C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
  (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
  (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero
  lower_zero C1 T T0 KP QP))) e0
    (@Product_pair_grpd (@computational_exact_at_selected C P t (@computational_abelian_preabelian C P t Ab) (@fapp0
      (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
      (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C
      P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian
      C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am
      Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
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
      B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_second_pair C P t Ab Am Bm Dm
      A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP))
      (@computational_exact_at_selected C P t (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat
      C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
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
      D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP)) e1 e2);

symbol homology_whole_exact_window_first [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (result : τ (@HomologyWholeExactWindow C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP)) : τ (@computational_exact_at_selected C P t
    (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Am A0 A1 (@short_exact_row_chain_source_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) C1 t T T0 (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t (@computational_abelian_preabelian C P
    t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t (@computational_abelian_preabelian C
    P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t (@computational_abelian_preabelian C P t Ab) Am Bm
    Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP Dm D0 D1 (@homology_connecting_step_right_pair C P t Ab A0
    B0 D0 A1 B1 D1 Dm row0 row1 G (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) Am Bm Dm A0 B0 D0 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm rowm) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) F) (@short_exact_row_chain_target_zero_path C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))))
    (@homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP))
≔ sigma_Fst result;

symbol homology_whole_exact_window_second [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (result : τ (@HomologyWholeExactWindow C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP)) : τ (@computational_exact_at_selected C P t
    (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
    (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C (@computational_homology_preadditive
    C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels C P t
    (@computational_abelian_preabelian C P t Ab)) KP Bm B0 B1 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G upper_zero))) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t
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
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@homology_whole_window_second_pair C P t Ab Am Bm Dm A0 B0
    D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J upper_zero lower_zero C1 T T0 KP QP))
≔ sigma_Fst (sigma_Snd result);

symbol homology_whole_exact_window_third [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
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
    Ab)) t T0 (@preabelian_cokernels C P t (@computational_abelian_preabelian C P t Ab))))
  (result : τ (@HomologyWholeExactWindow C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP)) : τ (@computational_exact_at_selected C P t
    (@computational_abelian_preabelian C P t Ab) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func
    C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) C1 t T T0
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
    D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero))) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
    P t Ab)) C1 t T T0 (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@preabelian_cokernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP QP) (@chain_pair_zero_cone C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) t T (@preabelian_kernels
    C P t (@computational_abelian_preabelian C P t Ab)) KP B0 B1 B2 (@short_exact_row_chain_middle_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J lower_zero)))
    (@homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1 row2 F G J
    upper_zero lower_zero C1 T T0 KP QP))
≔ sigma_Snd (sigma_Snd result);
