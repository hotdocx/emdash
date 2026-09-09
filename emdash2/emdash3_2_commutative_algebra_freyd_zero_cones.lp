/* The existing Freyd category satisfies the existing OneCat profile. */
require open emdash.emdash3_2_commutative_algebra_freyd_presentations;

symbol comm_ring_freyd_cat_is_one_cat (R : τ CommRing)
  : τ (IsNCat (cat_succ cat_zero) (@CommRingFreydPresentation_cat R))
≔ λ P : τ (@CommRingPresentation R), λ Q : τ (@CommRingPresentation R),
    @discrete_cat_intro (Path_cat (@CommRingFreydHomSet R P Q))
      (@comm_ring_freyd_hom_set_is_set R P Q)
      (@path_cat_is_groupoidal (@CommRingFreydHomSet R P Q));

symbol comm_ring_freyd_one_cat (R : τ CommRing) : τ OneCat
≔ @Struct_ncat (cat_succ cat_zero) (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_cat_is_one_cat R);

require open emdash.emdash3_2_one_cat_zero_cones;
require open emdash.emdash3_2_commutative_algebra_freyd_terminal_zero;

/* Model-facing alias: no explicit truncation/profile input for the user. */

symbol freyd_zero_cone_universal_transf (R : τ CommRing)
  : τ (@Transf
      (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
      (@comp_cat_fapp0
        (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
          (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
        (@CommRingFreydPresentation_cat R)
        (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
        (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R)
          (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
        (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R)
          (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
      (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
≔ @zero_arrow_cone_universal_transf (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R);
