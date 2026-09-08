/*
  Shared raw presentation and weak-pullback compatibility paths.

  These three rule-free paths relate transparent matrix operations to the
  generic finite-free category. The legacy kernel helper names delegate here;
  no kernel choice, selector, quotient decoder, or new equation is assumed.
*/

require open emdash.emdash3_2_commutative_algebra_finite_free_weak_pullbacks;
require open emdash.emdash3_2_commutative_algebra_freyd_cokernels;

symbol comm_ring_finite_free_weak_pullback_matrix_compatibility [R : τ CommRing]
  [x y z : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)] [b : τ (@CommRingMatrix R y z)]
  (U : τ (@CommRingFiniteFreeWeakPullback R x y z a b))
  : τ (@= (@CommRingMatrix R y (@comm_ring_finite_free_weak_pullback_rank R x y z a b U))
    (@comm_ring_matrix_comp R y x (@comm_ring_finite_free_weak_pullback_rank R x y z a b U)
      a (@comm_ring_finite_free_weak_pullback_proj1 R x y z a b U))
    (@comm_ring_matrix_comp R y z (@comm_ring_finite_free_weak_pullback_rank R x y z a b U)
      b (@comm_ring_finite_free_weak_pullback_proj2 R x y z a b U)))
≔ @eq_trans _ _
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_weak_pullback_rank R x y z a b U) x y
      a (@comm_ring_finite_free_weak_pullback_proj1 R x y z a b U)) _
    (@eq_sym _ _ _ (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_finite_free_weak_pullback_rank R x y z a b U) x y
      a (@comm_ring_finite_free_weak_pullback_proj1 R x y z a b U)))
    (@eq_trans _ _
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_weak_pullback_rank R x y z a b U) z y
        b (@comm_ring_finite_free_weak_pullback_proj2 R x y z a b U)) _
      (@computational_weak_pullback_compatibility_path
        (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_direct_sum_func R)
        zero (@comm_ring_finite_free_additive R) x y z a b U)
      (@comm_ring_finite_free_comp_fapp0_transparent_path R
        (@comm_ring_finite_free_weak_pullback_rank R x y z a b U) z y
        b (@comm_ring_finite_free_weak_pullback_proj2 R x y z a b U)));

// Raw relation preservation in the generic finite-free composition owner.
symbol comm_ring_presentation_morphism_finite_free_law
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R P))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_morphism_witness R P Q f))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_presentation_matrix R P)))
≔ @eq_trans _ _
    (@comm_ring_matrix_comp R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_witness R P Q f))
    _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_relations R P)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_matrix R Q)
      (@comm_ring_presentation_morphism_witness R P Q f))
    (@eq_trans _ _
      (@comm_ring_matrix_comp R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_relations R P)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_presentation_matrix R P))
      _
      (@comm_ring_presentation_morphism_law R P Q f)
      (@eq_sym _ _ _
        (@comm_ring_finite_free_comp_fapp0_transparent_path R
          (@comm_ring_presentation_relations R P)
          (@comm_ring_presentation_generators R P)
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_morphism_map R P Q f)
          (@comm_ring_presentation_matrix R P))));

symbol comm_ring_presentation_zero_agreement_finite_free_path
  [R : τ CommRing]
  [P Q T : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  (tau : τ (@CommRingPresentationMorphism R T P))
  (a : τ (@CommRingPresentationMorphismAgreement R T Q
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_zero R T Q))))
  : τ (@= (@CommRingMatrix R
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_generators R T))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_morphism_map R P Q f)
        (@comm_ring_presentation_morphism_map R T P tau))
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_matrix R Q)
        (@comm_ring_presentation_agreement_witness R T Q
          (@comm_ring_presentation_morphism_map R T Q
            (@comm_ring_presentation_morphism_comp R T P Q f tau))
          (@comm_ring_presentation_morphism_map R T Q
            (@comm_ring_presentation_morphism_zero R T Q))
          a)))
≔ @eq_trans _ _
    (@comm_ring_presentation_morphism_map R T Q
      (@comm_ring_presentation_morphism_comp R T P Q f tau))
    _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      (@comm_ring_presentation_generators R T)
      (@comm_ring_presentation_generators R P)
      (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R T P tau))
    (@eq_trans _ _
      (@comm_ring_matrix_sub R
        (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_generators R T)
        (@comm_ring_presentation_morphism_map R T Q
          (@comm_ring_presentation_morphism_comp R T P Q f tau))
        (@comm_ring_presentation_morphism_map R T Q
          (@comm_ring_presentation_morphism_zero R T Q)))
      _
      (@eq_sym _ _ _
        (@comm_ring_freyd_cokernel_sub_zero_path R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_morphism_map R T Q
            (@comm_ring_presentation_morphism_comp R T P Q f tau))))
      (@eq_trans _ _
        (@comm_ring_matrix_comp R
          (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_generators R T)
          (@comm_ring_presentation_matrix R Q)
          (@comm_ring_presentation_agreement_witness R T Q
            (@comm_ring_presentation_morphism_map R T Q
              (@comm_ring_presentation_morphism_comp R T P Q f tau))
            (@comm_ring_presentation_morphism_map R T Q
              (@comm_ring_presentation_morphism_zero R T Q))
            a))
        _
        (@eq_sym _ _ _
          (@comm_ring_presentation_agreement_law R T Q
            (@comm_ring_presentation_morphism_map R T Q
              (@comm_ring_presentation_morphism_comp R T P Q f tau))
            (@comm_ring_presentation_morphism_map R T Q
              (@comm_ring_presentation_morphism_zero R T Q))
            a))
        (@eq_sym _ _ _
          (@comm_ring_finite_free_comp_fapp0_transparent_path R
            (@comm_ring_presentation_generators R T)
            (@comm_ring_presentation_relations R Q)
            (@comm_ring_presentation_generators R Q)
            (@comm_ring_presentation_matrix R Q)
            (@comm_ring_presentation_agreement_witness R T Q
              (@comm_ring_presentation_morphism_map R T Q
                (@comm_ring_presentation_morphism_comp R T P Q f tau))
              (@comm_ring_presentation_morphism_map R T Q
                (@comm_ring_presentation_morphism_zero R T Q))
              a)))));
