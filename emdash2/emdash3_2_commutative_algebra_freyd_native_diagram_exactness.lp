/* Model view of the fixed-input certificate over the actual finite observation diagram. */
require open emdash.emdash3_2_one_cat_native_exact_diagrams;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_normality;
require open emdash.emdash3_2_commutative_algebra_freyd_diagram_observations;

// A transparent carrier view, not a new category or another input representation.
symbol FreydNativeInput (R : τ CommRing) : Grpd
≔ Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)));

symbol FreydNativeObservedPairExactAt [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M))
 (X : τ (FreydNativeInput R)) (a0 a1 : τ (FreydArrowObservation R)) : Grpd
≔ @NativeObservedPairExactAt (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N X a0 a1;

symbol FreydNativeObservedExactTail [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M))
 (n : τ Nat_grpd) (inputs : τ (@FiniteFamily (FreydNativeInput R) n))
 (first : τ (FreydArrowObservation R)) (arrows : τ (@FiniteFamily (FreydArrowObservation R) n)) : Grpd
≔ @NativeObservedExactTail (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N n inputs first arrows;

symbol freyd_native_observed_exact_tail_nil [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M)) (first : τ (FreydArrowObservation R))
 : τ (@FreydNativeObservedExactTail R M N zero (@finite_family_nil (FreydNativeInput R)) first
  (@finite_family_nil (FreydArrowObservation R)))
≔ @native_observed_exact_tail_nil (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N first;

symbol freyd_native_observed_exact_tail_cons [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M)) [n : τ Nat_grpd]
 [X0 : τ (FreydNativeInput R)] [inputs : τ (@FiniteFamily (FreydNativeInput R) n)]
 [a0 a1 : τ (FreydArrowObservation R)] [arrows : τ (@FiniteFamily (FreydArrowObservation R) n)]
 (E : τ (@FreydNativeObservedPairExactAt R M N X0 a0 a1))
 (rest : τ (@FreydNativeObservedExactTail R M N n inputs a1 arrows))
 : τ (@FreydNativeObservedExactTail R M N (succ n) (@finite_family_cons (FreydNativeInput R) n X0 inputs)
   a0 (@finite_family_cons (FreydArrowObservation R) n a1 arrows))
≔ @native_observed_exact_tail_cons (@CommRingFreydPresentation_cat R) (@additive_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@comm_ring_freyd_additive R)) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R)
  (@additive_terminal_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_additive R)) (@freyd_adjunction_model_initial R M)
  (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) N n X0 inputs a0 a1 arrows E
  rest;

symbol FreydNativeDiagramExactness [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M)) (n : τ Nat_grpd)
 (inputs : τ (@FiniteFamily (FreydNativeInput R) n)) (d : τ (FreydArrowObservationDiagram R n)) : Grpd
≔ @FreydNativeObservedExactTail R M N n inputs
 (@finite_family_head (FreydArrowObservation R) n (@freyd_arrow_diagram_arrows R n d))
 (@finite_family_tail (FreydArrowObservation R) n (@freyd_arrow_diagram_arrows R n d));

// Coverage is structural: exactly one retained native input/certificate for each adjacent arrow pair.
symbol freyd_native_exact_diagram_intro [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
 (N : τ (@FreydAdjunctionModelNormality R M)) [n : τ Nat_grpd]
 (inputs : τ (@FiniteFamily (FreydNativeInput R) n)) (first : τ (FreydArrowObservation R)) (arrows : τ
  (@FiniteFamily (FreydArrowObservation R) n))
 (matching : τ (@FreydArrowMatchingTail R first n arrows))
 (E : τ (@FreydNativeObservedExactTail R M N n inputs first arrows))
 : τ (@FreydNativeDiagramExactness R M N n inputs (@freyd_arrow_diagram_intro R n first arrows matching))
≔ E;
