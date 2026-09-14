/* Supplied whole P/Q over the existing Freyd category. This context contains
   no ordinary kernel/cokernel dictionaries and constructs no closed model. */
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cones;
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;

// Ordinary structure and the selected zero object are already fixed by R.
symbol FreydAdjunctionModel (R : τ CommRing) : Grpd
≔ `Σ_ Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R))
    (@comm_ring_zero_presentation R)),
    @Product_grpd
      (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
        (@comm_ring_freyd_terminal_zero R))
      (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z);

// Retain the supplied whole structures without selecting any ordinary views.
symbol freyd_adjunction_model_intro [R : τ CommRing]
  (Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R))
    (@comm_ring_zero_presentation R)))
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z))
  : τ (FreydAdjunctionModel R)
≔ Struct_sigma Z (Product_pair_grpd P Q);

symbol freyd_adjunction_model_initial [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R))
      (@comm_ring_zero_presentation R))
≔ sigma_Fst M;

symbol freyd_adjunction_model_kernels [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
      (@comm_ring_freyd_terminal_zero R))
≔ sigma_Fst (sigma_Snd M);

symbol freyd_adjunction_model_cokernels [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
      (@freyd_adjunction_model_initial R M))
≔ sigma_Snd (sigma_Snd M);

// The existing whole H; native input is formed independently of this context.
symbol freyd_adjunction_model_func [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R))
  : τ (Functor
      (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@CommRingFreydPresentation_cat R))
≔ @zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
    (@freyd_adjunction_model_initial R M)
    (@freyd_adjunction_model_kernels R M)
    (@freyd_adjunction_model_cokernels R M);
