/* Two adjacent generic windows: shared lower/upper H inputs and inclusion.
   All declarations below are local test assumptions or transparent views.
   No equality axiom, rewrite, unifier, endpoint cast or new H selection. */
require open emdash.emdash3_2_homology_window;

constant symbol C : Cat;
constant symbol P : τ (Functor (Product_cat C C) C);
constant symbol t : τ (Obj C);
constant symbol Ab : τ (@ComputationalAbelianCategory C P t);
symbol PA : τ (@PreAbelianCategory C P t) ≔ @computational_abelian_preabelian C P t Ab;
symbol S : τ (@PreadditiveCategory C) ≔ @computational_homology_preadditive C P t PA;
constant symbol C1 : τ (IsNCat (cat_succ cat_zero) C);
constant symbol T : τ (@TerminalObject C t);
constant symbol T0 : τ (@TerminalObject (Op_cat C) t);
constant symbol KP : τ (@KernelPresentation C S t T (@preabelian_kernels C P t PA));
constant symbol QP : τ (@CokernelPresentation C S t T0 (@preabelian_cokernels C P t PA));
symbol H : τ (Functor (@ZeroArrowCone_cat C t T) C)
≔ @zero_arrow_cone_homology_func C S C1 t T T0
  (@preabelian_kernels C P t PA) (@preabelian_cokernels C P t PA) KP QP;

constant symbol Am : τ (Obj C);
constant symbol Bm : τ (Obj C);
constant symbol Dm : τ (Obj C);
constant symbol rowm : τ (@ComputationalShortExactRow C P t PA Am Bm Dm);
symbol pairm : τ (@ComputationalChainPair C S Am Bm Dm)
≔ @computational_short_exact_row_pair C P t PA Am Bm Dm rowm;

constant symbol A0 : τ (Obj C);
constant symbol B0 : τ (Obj C);
constant symbol D0 : τ (Obj C);
constant symbol row0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0);
symbol pair0 : τ (@ComputationalChainPair C S A0 B0 D0)
≔ @computational_short_exact_row_pair C P t PA A0 B0 D0 row0;

constant symbol A1 : τ (Obj C);
constant symbol B1 : τ (Obj C);
constant symbol D1 : τ (Obj C);
constant symbol row1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1);
symbol pair1 : τ (@ComputationalChainPair C S A1 B1 D1)
≔ @computational_short_exact_row_pair C P t PA A1 B1 D1 row1;

constant symbol A2 : τ (Obj C);
constant symbol B2 : τ (Obj C);
constant symbol D2 : τ (Obj C);
constant symbol row2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2);
symbol pair2 : τ (@ComputationalChainPair C S A2 B2 D2)
≔ @computational_short_exact_row_pair C P t PA A2 B2 D2 row2;

constant symbol A3 : τ (Obj C);
constant symbol B3 : τ (Obj C);
constant symbol D3 : τ (Obj C);
constant symbol row3 : τ (@ComputationalShortExactRow C P t PA A3 B3 D3);
symbol pair3 : τ (@ComputationalChainPair C S A3 B3 D3)
≔ @computational_short_exact_row_pair C P t PA A3 B3 D3 row3;

constant symbol F : τ (@ComputationalChainPairMap C S Am Bm Dm A0 B0 D0 pairm pair0);
symbol bF : τ (Hom C Bm B0)
≔ @computational_chain_pair_map_middle C S Am Bm Dm A0 B0 D0 pairm pair0 F;
constant symbol G : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 pair0 pair1);
symbol bG : τ (Hom C B0 B1)
≔ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 pair0 pair1 G;
constant symbol J : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 pair1 pair2);
symbol bJ : τ (Hom C B1 B2)
≔ @computational_chain_pair_map_middle C S A1 B1 D1 A2 B2 D2 pair1 pair2 J;
constant symbol L : τ (@ComputationalChainPairMap C S A2 B2 D2 A3 B3 D3 pair2 pair3);
symbol bL : τ (Hom C B2 B3)
≔ @computational_chain_pair_map_middle C S A2 B2 D2 A3 B3 D3 pair2 pair3 L;
constant symbol z0 : τ (@= (Hom C Bm B1)
  (@comp_fapp0 C Bm B0 B1 bG bF)
  (@preadditive_hom_zero C S Bm B1));
constant symbol z1 : τ (@= (Hom C B0 B2)
  (@comp_fapp0 C B0 B1 B2 bJ bG)
  (@preadditive_hom_zero C S B0 B2));
constant symbol z2 : τ (@= (Hom C B1 B3)
  (@comp_fapp0 C B1 B2 B3 bL bJ)
  (@preadditive_hom_zero C S B1 B3));
symbol colA0 : τ (@ComputationalChainPair C S Am A0 A1)
≔ @short_exact_row_chain_source_pair C P t PA Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G z0;
symbol colB0 : τ (@ComputationalChainPair C S Bm B0 B1)
≔ @short_exact_row_chain_middle_pair C P t PA Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G z0;
symbol colD0 : τ (@ComputationalChainPair C S Dm D0 D1)
≔ @homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 Dm row0 row1 G
  (@computational_chain_pair_map_prev C S Am Bm Dm A0 B0 D0 pairm pair0 F)
  (@short_exact_row_chain_target_zero_path C P t PA Am Bm Dm A0 B0 D0 A1 B1 D1 rowm row0 row1 F G z0);
symbol HA0 : τ (Obj C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) C H
  (@chain_pair_zero_cone C S t T (@preabelian_kernels C P t PA) KP Am A0 A1 colA0);
symbol HB0 : τ (Obj C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) C H
  (@chain_pair_zero_cone C S t T (@preabelian_kernels C P t PA) KP Bm B0 B1 colB0);
symbol HD0 : τ (Obj C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) C H
  (@chain_pair_zero_cone C S t T (@preabelian_kernels C P t PA) KP Dm D0 D1 colD0);
symbol colA1 : τ (@ComputationalChainPair C S A0 A1 A2)
≔ @short_exact_row_chain_source_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J z1;
symbol colB1 : τ (@ComputationalChainPair C S B0 B1 B2)
≔ @short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J z1;
symbol colD1 : τ (@ComputationalChainPair C S D0 D1 D2)
≔ @homology_connecting_step_right_pair C P t Ab A1 B1 D1 A2 B2 D2 D0 row1 row2 J
  (@computational_chain_pair_map_prev C S A0 B0 D0 A1 B1 D1 pair0 pair1 G)
  (@short_exact_row_chain_target_zero_path C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 row0 row1 row2 G J z1);
symbol HA1 : τ (Obj C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) C H
  (@chain_pair_zero_cone C S t T (@preabelian_kernels C P t PA) KP A0 A1 A2 colA1);
symbol HB1 : τ (Obj C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) C H
  (@chain_pair_zero_cone C S t T (@preabelian_kernels C P t PA) KP B0 B1 B2 colB1);
symbol HD1 : τ (Obj C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) C H
  (@chain_pair_zero_cone C S t T (@preabelian_kernels C P t PA) KP D0 D1 D2 colD1);

symbol upper_third
≔ @homology_whole_window_third_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  rowm row0 row1 row2 F G J z0 z1 C1 T T0 KP QP;

symbol lower_first
≔ @homology_whole_window_first_pair C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3
  row0 row1 row2 row3 G J L z1 z2 C1 T T0 KP QP;

// Infer endpoints from the existing owners instead of rechecking readability aliases.
symbol shared_upper ≔ computational_chain_pair_d upper_third;
symbol shared_lower ≔ computational_chain_pair_dnext lower_first;
assert ⊢ shared_upper ≡ shared_lower;


/* Two real exact windows, sharing the original H-inclusion boundary. */
require open emdash.emdash3_2_finite_arrow_tail_append;
require open emdash.emdash3_2_computational_exact_arrow_tails;
require open emdash.emdash3_2_homology_exact_window_result;

symbol upper_first ≔ @homology_whole_window_first_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1
  row2 F G J z0 z1 C1 T T0 KP QP;
symbol upper_first_exact ≔ @homology_whole_window_first_exact C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0
  row1 row2 F G J z0 z1 C1 T T0 KP QP;
symbol upper_second ≔ @homology_whole_window_second_pair C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0 row1
  row2 F G J z0 z1 C1 T T0 KP QP;
symbol upper_second_exact ≔ @homology_whole_window_second_exact C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm
  row0 row1 row2 F G J z0 z1 C1 T T0 KP QP;
symbol upper_third_exact ≔ @homology_whole_window_third_exact C P t Ab Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 rowm row0
  row1 row2 F G J z0 z1 C1 T T0 KP QP;
symbol upper_tail ≔ computational_exact_arrow_tail_cons_pair PA upper_first upper_first_exact
  (computational_exact_arrow_tail_cons_pair PA upper_second upper_second_exact
    (computational_exact_arrow_tail_cons_pair PA upper_third upper_third_exact
      (computational_exact_arrow_tail_nil PA)));

symbol lower_first_exact ≔ @homology_whole_window_first_exact C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3 row0 row1
  row2 row3 G J L z1 z2 C1 T T0 KP QP;
symbol lower_second ≔ @homology_whole_window_second_pair C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3 row0 row1 row2
  row3 G J L z1 z2 C1 T T0 KP QP;
symbol lower_second_exact ≔ @homology_whole_window_second_exact C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3 row0
  row1 row2 row3 G J L z1 z2 C1 T T0 KP QP;
symbol lower_third ≔ @homology_whole_window_third_pair C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3 row0 row1 row2
  row3 G J L z1 z2 C1 T T0 KP QP;
symbol lower_third_exact ≔ @homology_whole_window_third_exact C P t Ab A0 B0 D0 A1 B1 D1 A2 B2 D2 A3 B3 D3 row0 row1
  row2 row3 G J L z1 z2 C1 T T0 KP QP;
symbol lower_tail ≔ computational_exact_arrow_tail_cons_pair PA lower_first lower_first_exact
  (computational_exact_arrow_tail_cons_pair PA lower_second lower_second_exact
    (computational_exact_arrow_tail_cons_pair PA lower_third lower_third_exact
      (computational_exact_arrow_tail_nil PA)));

symbol Q ≔ @ComputationalExactArrowStep C P t PA;
symbol three : τ Nat_grpd ≔ succ (succ (succ zero));
symbol joined ≔ finite_arrow_tail_append Q three three upper_tail lower_tail;
symbol tail_after_three ≔ finite_arrow_tail_rest Q
  (finite_arrow_tail_rest Q (finite_arrow_tail_rest Q joined));

assert ⊢ finite_arrow_tail_last_arrow Q three upper_tail ≡ shared_upper;
assert ⊢ tail_after_three ≡ lower_tail;
assert ⊢ finite_arrow_tail_step Q joined
  ≡ computational_exact_arrow_step_of_pair PA upper_first upper_first_exact;
assert ⊢ finite_arrow_tail_last_arrow Q (nat_add three three) joined
  ≡ computational_chain_pair_d lower_third;
