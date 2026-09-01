/*
  Quotient pairing and whole direct sums in the formal Freyd category.

  Pairing descends through agreement groupoidification and 0-truncation by the
  same whole-extension architecture as Freyd addition. Arrow direct sum is
  then derived as `<f o pi_1,g o pi_2>`, so no duplicate binary quotient
  descent is introduced. The resulting whole functor retains every Hom action.
*/

require open emdash.emdash3_2_commutative_algebra_presentation_direct_sum_agreements;
require open emdash.emdash3_2_commutative_algebra_freyd_preadditive;

// With the left raw map fixed, pairing acts functorially on right agreements.
injective symbol comm_ring_presentation_pair_right_agreement_func
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R X P))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R X Q)
      (@CommRingPresentationAgreement_cat R X
        (@comm_ring_presentation_direct_sum R P Q)));

rule @fapp0 _ _
      (@comm_ring_presentation_pair_right_agreement_func
        $R $X $P $Q $f) $g
  ↪ @comm_ring_presentation_pair $R $X $P $Q $f $g;

// Rigid first-arrow action of fixed-left pairing.
injective symbol comm_ring_presentation_pair_right_agreement_fapp1
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R X P)]
  [g g' : τ (@CommRingPresentationMorphism R X Q)]
  (b : τ (@CommRingPresentationMorphismAgreement R X Q
      (@comm_ring_presentation_morphism_map R X Q g)
      (@comm_ring_presentation_morphism_map R X Q g')))
  : τ (@CommRingPresentationMorphismAgreement R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f g))
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f g')));

// Proof-time comparison keeps generic fapp1 out of the runtime evaluator.
unif_rule
  @fapp1_fapp0 _ _
      (@comm_ring_presentation_pair_right_agreement_func
        $R $X $P $Q $f) $g $g' $b
  ≡ @comm_ring_presentation_pair_right_agreement_fapp1
      $R $X $P $Q $f $g $g' $b
  ↪ [ tt ≡ tt ];

symbol comm_ring_presentation_pair_right_agreement_fapp1_path
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f : τ (@CommRingPresentationMorphism R X P)]
  [g g' : τ (@CommRingPresentationMorphism R X Q)]
  (b : τ (@CommRingPresentationMorphismAgreement R X Q
      (@comm_ring_presentation_morphism_map R X Q g)
      (@comm_ring_presentation_morphism_map R X Q g')))
  : τ (@= (@CommRingPresentationMorphismAgreement R X
      (@comm_ring_presentation_direct_sum R P Q)
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f g))
      (@comm_ring_presentation_morphism_map R X
        (@comm_ring_presentation_direct_sum R P Q)
        (@comm_ring_presentation_pair R X P Q f g')))
      (@fapp1_fapp0
        (@CommRingPresentationAgreement_cat R X Q)
        (@CommRingPresentationAgreement_cat R X
          (@comm_ring_presentation_direct_sum R P Q))
        (@comm_ring_presentation_pair_right_agreement_func R X P Q f)
        g g' b)
      (@comm_ring_presentation_pair_right_agreement_fapp1
        R X P Q f g g' b))
≔ @eq_refl _
    (@fapp1_fapp0
      (@CommRingPresentationAgreement_cat R X Q)
      (@CommRingPresentationAgreement_cat R X
        (@comm_ring_presentation_direct_sum R P Q))
      (@comm_ring_presentation_pair_right_agreement_func R X P Q f)
      g g' b);

// The rigid action exposes the already-constructed paired agreement.
rule @comm_ring_presentation_pair_right_agreement_fapp1
      $R $X $P $Q $f $g $g' $b
  ↪ @comm_ring_presentation_pair_agreement
      $R $X $P $Q $f $f $g $g'
      (@comm_ring_presentation_agreement_refl
        $R $X $P
        (@comm_ring_presentation_morphism_map $R $X $P $f))
      $b;

// Path-valued representation of fixed-left raw pairing.
symbol comm_ring_freyd_pair_right_representation_func
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R X P))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R X Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q))))
≔ @comp_cat_fapp0
    (@CommRingPresentationAgreement_cat R X Q)
    (@CommRingPresentationAgreement_cat R X
      (@comm_ring_presentation_direct_sum R P Q))
    (Path_cat (@CommRingFreydRawHomGroupoid R X
      (@comm_ring_presentation_direct_sum R P Q)))
    (@groupoidify_unit_func
      (@CommRingPresentationAgreement_cat R X
        (@comm_ring_presentation_direct_sum R P Q)))
    (@comm_ring_presentation_pair_right_agreement_func R X P Q f);

// Raw function `g |-> <f,g>` obtained by groupoidification extension.
symbol comm_ring_freyd_raw_pair_right_function
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R X P))
  : τ (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
≔ @groupoidify_extend_at
    (@CommRingPresentationAgreement_cat R X Q)
    (@CommRingFreydRawHomGroupoid R X
      (@comm_ring_presentation_direct_sum R P Q))
    (@comm_ring_freyd_pair_right_representation_func R X P Q f);

// Varying the fixed left map gives a whole transformation of representations.
injective symbol comm_ring_freyd_pair_right_representation_transf
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R X P)]
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  : τ (@Transf
      (@CommRingPresentationAgreement_cat R X Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
      (@comm_ring_freyd_pair_right_representation_func R X P Q f)
      (@comm_ring_freyd_pair_right_representation_func R X P Q f'));

rule @tapp0_fapp0 _ _ _ _ $g
      (@comm_ring_freyd_pair_right_representation_transf
        $R $X $P $Q $f $f' $a)
  ↪ @comm_ring_freyd_raw_agreement_path
      $R $X (@comm_ring_presentation_direct_sum $R $P $Q)
      (@comm_ring_presentation_pair $R $X $P $Q $f $g)
      (@comm_ring_presentation_pair $R $X $P $Q $f' $g)
      (@comm_ring_presentation_pair_agreement
        $R $X $P $Q $f $f' $g $g
        $a
        (@comm_ring_presentation_agreement_refl
          $R $X $Q
          (@comm_ring_presentation_morphism_map $R $X $Q $g)));

// Whole path between fixed-left raw pairing functions.
symbol comm_ring_freyd_raw_pair_right_function_path
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R X P)]
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  : τ (@= (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
      (@comm_ring_freyd_raw_pair_right_function R X P Q f)
      (@comm_ring_freyd_raw_pair_right_function R X P Q f'))
≔ @fapp1_fapp0
    (@Functor_cat
      (@CommRingPresentationAgreement_cat R X Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q))))
    (@Hom_cat Grpd_cat
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
    (@groupoidify_extend_func
      (@CommRingPresentationAgreement_cat R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
    (@comm_ring_freyd_pair_right_representation_func R X P Q f)
    (@comm_ring_freyd_pair_right_representation_func R X P Q f')
    (@comm_ring_freyd_pair_right_representation_transf R X P Q f f' a);

// Outer representation of the varying fixed-left pairing function.
injective symbol comm_ring_freyd_raw_pair_outer_representation_func
  (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R X P)
      (Path_cat (@Function_grpd
        (@CommRingFreydRawHomGroupoid R X Q)
        (@CommRingFreydRawHomGroupoid R X
          (@comm_ring_presentation_direct_sum R P Q)))));

rule @fapp0 _ _
      (@comm_ring_freyd_raw_pair_outer_representation_func
        $R $X $P $Q) $f
  ↪ @comm_ring_freyd_raw_pair_right_function $R $X $P $Q $f;

// Rigid outer first-arrow action; the semantic function path is too reducible
// to serve directly as a unification discriminator.
injective symbol comm_ring_freyd_raw_pair_outer_action
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R X P)]
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  : τ (@= (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
      (@comm_ring_freyd_raw_pair_right_function R X P Q f)
      (@comm_ring_freyd_raw_pair_right_function R X P Q f'));

// Proof-time outer action comparison against the rigid intermediary.
unif_rule
  @fapp1_fapp0 _ _
      (@comm_ring_freyd_raw_pair_outer_representation_func
        $R $X $P $Q) $f $f' $a
  ≡ @comm_ring_freyd_raw_pair_outer_action
      $R $X $P $Q $f $f' $a
  ↪ [ tt ≡ tt ];

symbol comm_ring_freyd_raw_pair_outer_action_path
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R X P)]
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  : τ (@= (@= (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
      (@comm_ring_freyd_raw_pair_right_function R X P Q f)
      (@comm_ring_freyd_raw_pair_right_function R X P Q f'))
      (@fapp1_fapp0
        (@CommRingPresentationAgreement_cat R X P)
        (Path_cat (@Function_grpd
          (@CommRingFreydRawHomGroupoid R X Q)
          (@CommRingFreydRawHomGroupoid R X
            (@comm_ring_presentation_direct_sum R P Q))))
        (@comm_ring_freyd_raw_pair_outer_representation_func R X P Q)
        f f' a)
      (@comm_ring_freyd_raw_pair_outer_action
        R X P Q f f' a))
≔ @eq_refl _
    (@fapp1_fapp0
      (@CommRingPresentationAgreement_cat R X P)
      (Path_cat (@Function_grpd
        (@CommRingFreydRawHomGroupoid R X Q)
        (@CommRingFreydRawHomGroupoid R X
          (@comm_ring_presentation_direct_sum R P Q))))
      (@comm_ring_freyd_raw_pair_outer_representation_func R X P Q)
      f f' a);

// After validating the proof-time bridge, expose its constructed semantics.
rule @comm_ring_freyd_raw_pair_outer_action
      $R $X $P $Q $f $f' $a
  ↪ @comm_ring_freyd_raw_pair_right_function_path
      $R $X $P $Q $f $f' $a;

symbol comm_ring_freyd_raw_pair_outer_action_semantic_path
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R X P)]
  (a : τ (@CommRingPresentationMorphismAgreement R X P
      (@comm_ring_presentation_morphism_map R X P f)
      (@comm_ring_presentation_morphism_map R X P f')))
  : τ (@= (@= (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
      (@comm_ring_freyd_raw_pair_right_function R X P Q f)
      (@comm_ring_freyd_raw_pair_right_function R X P Q f'))
      (@comm_ring_freyd_raw_pair_outer_action R X P Q f f' a)
      (@comm_ring_freyd_raw_pair_right_function_path R X P Q f f' a))
≔ @eq_refl _
    (@comm_ring_freyd_raw_pair_outer_action R X P Q f f' a);

// Curried raw pairing on the two groupoidified Hom carriers.
symbol comm_ring_freyd_raw_pair_curried
  (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  : τ (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X P)
      (@Function_grpd
        (@CommRingFreydRawHomGroupoid R X Q)
        (@CommRingFreydRawHomGroupoid R X
          (@comm_ring_presentation_direct_sum R P Q))))
≔ @groupoidify_extend_at
    (@CommRingPresentationAgreement_cat R X P)
    (@Function_grpd
      (@CommRingFreydRawHomGroupoid R X Q)
      (@CommRingFreydRawHomGroupoid R X
        (@comm_ring_presentation_direct_sum R P Q)))
    (@comm_ring_freyd_raw_pair_outer_representation_func R X P Q);

symbol comm_ring_freyd_raw_pair
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydRawHomGroupoid R X P))
  (g : τ (@CommRingFreydRawHomGroupoid R X Q))
  : τ (@CommRingFreydRawHomGroupoid R X
      (@comm_ring_presentation_direct_sum R P Q))
≔ (@comm_ring_freyd_raw_pair_curried R X P Q) f g;

// Ordinary quotient-Hom pairing by nested 0-truncation descent.
symbol comm_ring_freyd_pair
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R X P))
  (g : τ (@CommRingFreydHomSet R X Q))
  : τ (@CommRingFreydHomSet R X
      (@comm_ring_presentation_direct_sum R P Q))
≔ @trunc_rec_ambient
    trunc_zero
    (@CommRingFreydRawHomGroupoid R X P)
    (@CommRingFreydHomSet R X
      (@comm_ring_presentation_direct_sum R P Q))
    (@comm_ring_freyd_hom_set_is_set R X
      (@comm_ring_presentation_direct_sum R P Q))
    (λ raw_f : τ (@CommRingFreydRawHomGroupoid R X P),
      @trunc_map
        trunc_zero
        (@CommRingFreydRawHomGroupoid R X Q)
        (@CommRingFreydRawHomGroupoid R X
          (@comm_ring_presentation_direct_sum R P Q))
        (λ raw_g : τ (@CommRingFreydRawHomGroupoid R X Q),
          @comm_ring_freyd_raw_pair R X P Q raw_f raw_g)
        g)
    f;

// Selected quotient classes of the two raw projections.
symbol comm_ring_freyd_proj1_class
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) P)
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_presentation_direct_sum R P Q) P
    (@comm_ring_presentation_proj1 R P Q);

symbol comm_ring_freyd_proj2_class
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) Q)
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_presentation_direct_sum R P Q) Q
    (@comm_ring_presentation_proj2 R P Q);

// Arrow direct sum derived from pairing the two projection composites.
symbol comm_ring_freyd_direct_sum
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R P0 Q0))
  (g : τ (@CommRingFreydHomSet R P1 Q1))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P0 P1)
      (@comm_ring_presentation_direct_sum R Q0 Q1))
≔ @comm_ring_freyd_pair R
    (@comm_ring_presentation_direct_sum R P0 P1) Q0 Q1
    (@comm_ring_freyd_comp R
      (@comm_ring_presentation_direct_sum R P0 P1) P0 Q0
      f (@comm_ring_freyd_proj1_class R P0 P1))
    (@comm_ring_freyd_comp R
      (@comm_ring_presentation_direct_sum R P0 P1) P1 Q1
      g (@comm_ring_freyd_proj2_class R P0 P1));

// Whole presentation direct-sum functor with quotient-Hom arrow action.
injective symbol comm_ring_freyd_direct_sum_func
  (R : τ CommRing)
  : τ (@Functor
      (Product_cat
        (@CommRingFreydPresentation_cat R)
        (@CommRingFreydPresentation_cat R))
      (@CommRingFreydPresentation_cat R));

rule @fapp0 _ _
      (@comm_ring_freyd_direct_sum_func $R)
      (Struct_sigma $P $Q)
  ↪ @comm_ring_presentation_direct_sum $R $P $Q;

rule @fapp1_fapp0 _ _
      (@comm_ring_freyd_direct_sum_func $R)
      (Struct_sigma $P0 $P1)
      (Struct_sigma $Q0 $Q1)
      (Struct_sigma $f $g)
  ↪ @comm_ring_freyd_direct_sum
      $R $P0 $P1 $Q0 $Q1 $f $g;

// Retained first Hom action of the whole direct-sum functor.
symbol comm_ring_freyd_direct_sum_hom_func
  [R : τ CommRing]
  [P0 P1 Q0 Q1 : τ (@CommRingPresentation R)]
  : τ (@Functor
      (Hom_cat
        (Product_cat
          (@CommRingFreydPresentation_cat R)
          (@CommRingFreydPresentation_cat R))
        (Struct_sigma P0 P1)
        (Struct_sigma Q0 Q1))
      (Hom_cat
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_presentation_direct_sum R P0 P1)
        (@comm_ring_presentation_direct_sum R Q0 Q1)))
≔ @fapp1_func
    (Product_cat
      (@CommRingFreydPresentation_cat R)
      (@CommRingFreydPresentation_cat R))
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (Struct_sigma P0 P1)
    (Struct_sigma Q0 Q1);
