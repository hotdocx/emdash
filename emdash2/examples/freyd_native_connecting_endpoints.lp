/* Original raw window hypotheses; whole outputs reuse the existing native owners. */
require open emdash.emdash3_2_commutative_algebra_freyd_raw_window_connecting;
symbol K : Cat;
symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
symbol N : τ (@FreydAdjunctionModelNormality R M);
symbol Am : τ (@CommRingPresentation R);
symbol Bm : τ (@CommRingPresentation R);
symbol Dm : τ (@CommRingPresentation R);
symbol A0 : τ (@CommRingPresentation R);
symbol B0 : τ (@CommRingPresentation R);
symbol D0 : τ (@CommRingPresentation R);
symbol A1 : τ (@CommRingPresentation R);
symbol B1 : τ (@CommRingPresentation R);
symbol D1 : τ (@CommRingPresentation R);
symbol A2 : τ (@CommRingPresentation R);
symbol B2 : τ (@CommRingPresentation R);
symbol D2 : τ (@CommRingPresentation R);
symbol im : τ (@CommRingPresentationMorphism R Am Bm);
symbol pm : τ (@CommRingPresentationMorphism R Bm Dm);
symbol cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm);
symbol xm : τ (@FreydRawNativeRowShortExact K R M Am Bm Dm im pm cm);
symbol i0 : τ (@CommRingPresentationMorphism R A0 B0);
symbol p0 : τ (@CommRingPresentationMorphism R B0 D0);
symbol c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0);
symbol x0 : τ (@FreydRawNativeRowShortExact K R M A0 B0 D0 i0 p0 c0);
symbol i1 : τ (@CommRingPresentationMorphism R A1 B1);
symbol p1 : τ (@CommRingPresentationMorphism R B1 D1);
symbol c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1);
symbol x1 : τ (@FreydRawNativeRowShortExact K R M A1 B1 D1 i1 p1 c1);
symbol i2 : τ (@CommRingPresentationMorphism R A2 B2);
symbol p2 : τ (@CommRingPresentationMorphism R B2 D2);
symbol c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2);
symbol x2 : τ (@FreydRawNativeRowShortExact K R M A2 B2 D2 i2 p2 c2);
symbol am : τ (@CommRingPresentationMorphism R Am A0);
symbol bm : τ (@CommRingPresentationMorphism R Bm B0);
symbol dm : τ (@CommRingPresentationMorphism R Dm D0);
symbol fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm);
symbol a0 : τ (@CommRingPresentationMorphism R A0 A1);
symbol b0 : τ (@CommRingPresentationMorphism R B0 B1);
symbol d0 : τ (@CommRingPresentationMorphism R D0 D1);
symbol gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0);
symbol a1 : τ (@CommRingPresentationMorphism R A1 A2);
symbol b1 : τ (@CommRingPresentationMorphism R B1 B2);
symbol d1 : τ (@CommRingPresentationMorphism R D1 D2);
symbol jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1);
symbol upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0);
symbol lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1);

symbol HS : τ (Functor K (@CommRingFreydPresentation_cat R)) ≔ @one_cat_native_window_source_homology_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm)
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2;
symbol HT : τ (Functor K (@CommRingFreydPresentation_cat R)) ≔ @one_cat_native_window_target_homology_func K
  (@CommRingFreydPresentation_cat R) (@additive_preadditive (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R))
  (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@additive_terminal_object
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M)
  (@freyd_adjunction_model_cokernels R M) (@freyd_raw_native_row_family K R Am Bm Dm im pm cm)
  (@freyd_raw_native_row_family K R A0 B0 D0 i0 p0 c0) (@freyd_raw_native_row_family K R A1 B1 D1 i1 p1 c1)
  (@freyd_raw_native_row_family K R A2 B2 D2 i2 p2 c2) (@freyd_raw_native_row_map K R Am Bm Dm A0 B0 D0 im pm i0
  p0 am bm dm cm c0 fm) (@freyd_raw_native_row_map K R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm)
  (@freyd_raw_native_row_map K R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm)
  (@freyd_raw_native_row_middle_zero K R (@freyd_adjunction_model_initial R M) Am Bm Dm A0 B0 D0 A1 B1 D1 im pm
  i0 p0 i1 p1 am bm dm a0 b0 d0 cm c0 c1 fm gm upper) (@freyd_raw_native_row_middle_zero K R
  (@freyd_adjunction_model_initial R M) A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1 p1 i2 p2 a0 b0 d0 a1 b1 d1 c0 c1 c2
  gm jm lower) xm x0 x1 x2;
symbol delta ≔ @freyd_raw_native_window_connecting K R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0
  c0 x0 i1 p1 c1 x1 i2 p2 c2 x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower;
symbol x : τ (Obj K);
symbol y : τ (Obj K);

// One whole δ at the original native-window H endpoints.
require open emdash.emdash3_2_commutative_algebra_freyd_native_column_homology_comparisons;
symbol right_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0);
symbol left_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1);
symbol source_comparison ≔ @freyd_raw_native_right_column_homology_map K R M Am Bm Dm A0 B0 D0 A1 B1 D1 im pm i0
  p0 i1 p1 cm c0 c1 am bm dm a0 b0 d0 fm gm upper xm x right_chain;
symbol source_equiv ≔ @freyd_raw_native_right_column_homology_equiv K R M Am Bm Dm A0 B0 D0 A1 B1 D1 im pm i0 p0
  i1 p1 cm c0 c1 am bm dm a0 b0 d0 fm gm upper xm x right_chain;
symbol target_comparison ≔ @freyd_raw_native_left_column_homology_map K R M A0 B0 D0 A1 B1 D1 A2 B2 D2 i0 p0 i1
  p1 i2 p2 c0 c1 c2 a0 b0 d0 a1 b1 d1 gm jm lower x2 x left_chain;
assert ⊢ source_comparison : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat
  R) HS x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M)
  (@freyd_raw_chain_native_cone R Dm D0 D1 dm d0 right_chain)));
assert ⊢ target_comparison : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat
  R) HT x) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M)
  (@freyd_raw_chain_native_cone R A0 A1 A2 a0 a1 left_chain)));
assert ⊢ delta : τ (@Transf K (@CommRingFreydPresentation_cat R) HS HT);
assert ⊢ @tapp1_func K (@CommRingFreydPresentation_cat R) HS HT x y delta : τ (Functor (Hom_cat K x y) (Hom_cat
  (@CommRingFreydPresentation_cat R) (@fapp0 K (@CommRingFreydPresentation_cat R) HS x) (@fapp0 K
  (@CommRingFreydPresentation_cat R) HT y)));
assert ⊢ comp_fapp0 target_comparison (comp_fapp0 (@tapp0_fapp0 K (@CommRingFreydPresentation_cat R) HS HT x
  delta) (omega_equiv_along_left_inv source_equiv)) : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M)
  (@freyd_raw_chain_native_cone R Dm D0 D1 dm d0 right_chain)) (@fapp0 (@ZeroArrowCone_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
  (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_func R M) (@freyd_raw_chain_native_cone R A0 A1 A2
  a0 a1 left_chain)));
