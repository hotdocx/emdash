/* Original raw morphisms and their existing agreement suffice for whole row action. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_row_families;
symbol K : Cat;
symbol R : τ CommRing;
symbol S2 : τ (@CommRingPresentation R);
symbol S1 : τ (@CommRingPresentation R);
symbol S0 : τ (@CommRingPresentation R);
symbol T2 : τ (@CommRingPresentation R);
symbol T1 : τ (@CommRingPresentation R);
symbol T0 : τ (@CommRingPresentation R);
symbol sdNext : τ (@CommRingPresentationMorphism R S2 S1);
symbol sd : τ (@CommRingPresentationMorphism R S1 S0);
symbol tdNext : τ (@CommRingPresentationMorphism R T2 T1);
symbol td : τ (@CommRingPresentationMorphism R T1 T0);
symbol f2 : τ (@CommRingPresentationMorphism R S2 T2);
symbol f1 : τ (@CommRingPresentationMorphism R S1 T1);
symbol f0 : τ (@CommRingPresentationMorphism R S0 T0);
symbol chainS : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd);
symbol chainT : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td);
symbol m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0);
symbol x : τ (Obj K);
symbol y : τ (Obj K);
// Each row point is its original native raw input.
assert ⊢ @fapp0 K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) x ≡
  (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS);
// Each row-map component is the original native map.
assert ⊢ (@tapp0_fapp0 K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation
  R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS)
  (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT) x (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1
  T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)) ≡ (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext
  sd tdNext td f2 f1 f0 chainS chainT m);
// Retain an original raw morphism class after row-map observation.
assert ⊢ @fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_first_func
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
  (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext
  td chainT) (@tapp0_fapp0 K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1
  S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT) x
  (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)) ≡
  @comm_ring_freyd_hom_class R S2 T2 f2;
// Retain an original raw morphism class after row-map observation.
assert ⊢ @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) _ _ walking_arrow_src (@fapp1_fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)
  (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT) (@tapp0_fapp0 K (@ZeroArrowCone_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0
  tdNext td chainT) x (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS
  chainT m))) ≡ @comm_ring_freyd_hom_class R S1 T1 f1;
// Retain an original raw morphism class after row-map observation.
assert ⊢ @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) _ _ walking_arrow_tgt (@fapp1_fapp0
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
  (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)
  (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT) (@tapp0_fapp0 K (@ZeroArrowCone_cat
  (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
  (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0
  tdNext td chainT) x (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS
  chainT m))) ≡ @comm_ring_freyd_hom_class R S0 T0 f0;
// Whole off-diagonal action is inherited from the existing weakening owner.
assert ⊢ @tapp1_func K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS)
  (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT) x y (@freyd_raw_native_row_map K R S2 S1 S0 T2
  T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m) ≡ @Const_func (Hom_cat K x y) (Hom_cat
  (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)
  (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT)) (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0
  sdNext sd tdNext td f2 f1 f0 chainS chainT m);
// The raw-agreement parameter still has complete higher Hom action.
assert (m2 : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) ⊢
  @fapp1_func _ _ (@freyd_raw_native_row_map_func K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS
  chainT) m m2 : τ (Functor (Hom_cat (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd
  tdNext td f2 f1 f0)) m m2) (Hom_cat (@Transf_cat K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1
  S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT))
  (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  (@freyd_raw_native_row_map K R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m2)));
