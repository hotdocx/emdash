/*
  Whole composition and addition on groupoidified and 0-truncated Freyd Homs.

  Fixed raw operations act by whole functors on agreement categories. Their
  direct generic fapp1 runtime rules are deliberately avoided: proof-time
  unifiers meet stable agreement-action heads, while typed eq_refl theorem
  views validate firing. Whole transfors vary the fixed operand and existing
  groupoidification extension produces paths between the extended functions.
  Outer representations retain their constructed fapp1 runtime action; their
  six identity-action critical pairs are classified rather than used as a
  veto. Nested truncation recursion then gives ordinary quotient-Hom
  composition and addition with raw-class point computation.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_presentations;

injective symbol comm_ring_presentation_postcomp_agreement_func
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingPresentationAgreement_cat R P S));

rule @fapp0 _ _
      (@comm_ring_presentation_postcomp_agreement_func
        $R $P $Q $S $g) $f
  ↪ @comm_ring_presentation_morphism_comp $R $P $Q $S $g $f;

injective symbol comm_ring_presentation_postcomp_agreement_fapp1
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  [g : τ (@CommRingPresentationMorphism R Q S)]
  [f f' : τ (@CommRingPresentationMorphism R P Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q f')))
  : τ (@CommRingPresentationMorphismAgreement R P S
      (@comm_ring_presentation_morphism_comp_map R P Q S g f)
      (@comm_ring_presentation_morphism_comp_map R P Q S g f'));

unif_rule
  @fapp1_fapp0 _ _
      (@comm_ring_presentation_postcomp_agreement_func
        $R $P $Q $S $g) $f $f' $a
  ≡ @comm_ring_presentation_postcomp_agreement_fapp1
      $R $P $Q $S $g $f $f' $a
  ↪ [ tt ≡ tt ];

symbol comm_ring_presentation_postcomp_agreement_fapp1_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  [g : τ (@CommRingPresentationMorphism R Q S)]
  [f f' : τ (@CommRingPresentationMorphism R P Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q f')))
  : τ (@= (@CommRingPresentationMorphismAgreement R P S
      (@comm_ring_presentation_morphism_comp_map R P Q S g f)
      (@comm_ring_presentation_morphism_comp_map R P Q S g f'))
      (@fapp1_fapp0
        (@CommRingPresentationAgreement_cat R P Q)
        (@CommRingPresentationAgreement_cat R P S)
        (@comm_ring_presentation_postcomp_agreement_func R P Q S g)
        f f' a)
      (@comm_ring_presentation_postcomp_agreement_fapp1
        R P Q S g f f' a))
≔ @eq_refl
    (@CommRingPresentationMorphismAgreement R P S
      (@comm_ring_presentation_morphism_comp_map R P Q S g f)
      (@comm_ring_presentation_morphism_comp_map R P Q S g f'))
    (@fapp1_fapp0
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingPresentationAgreement_cat R P S)
      (@comm_ring_presentation_postcomp_agreement_func R P Q S g)
      f f' a);

symbol comm_ring_freyd_postcomp_representation_func
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R P S)))
≔ @comp_cat_fapp0
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingPresentationAgreement_cat R P S)
    (Path_cat (@CommRingFreydRawHomGroupoid R P S))
    (@groupoidify_unit_func
      (@CommRingPresentationAgreement_cat R P S))
    (@comm_ring_presentation_postcomp_agreement_func R P Q S g);

symbol comm_ring_freyd_raw_postcomp_function
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingPresentationMorphism R Q S))
  : τ (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P S))
≔ @groupoidify_extend_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydRawHomGroupoid R P S)
    (@comm_ring_freyd_postcomp_representation_func R P Q S g);

injective symbol comm_ring_freyd_postcomp_representation_transf
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  [g h : τ (@CommRingPresentationMorphism R Q S)]
  (a : τ (@CommRingPresentationMorphismAgreement R Q S
      (@comm_ring_presentation_morphism_map R Q S g)
      (@comm_ring_presentation_morphism_map R Q S h)))
  : τ (@Transf
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R P S))
      (@comm_ring_freyd_postcomp_representation_func R P Q S g)
      (@comm_ring_freyd_postcomp_representation_func R P Q S h));

rule @tapp0_fapp0 _ _ _ _ $f
      (@comm_ring_freyd_postcomp_representation_transf
        $R $P $Q $S $g $h $a)
  ↪ @comm_ring_freyd_raw_agreement_path
      $R $P $S
      (@comm_ring_presentation_morphism_comp $R $P $Q $S $g $f)
      (@comm_ring_presentation_morphism_comp $R $P $Q $S $h $f)
      (@comm_ring_presentation_agreement_precomp
        $R $P $Q $S
        (@comm_ring_presentation_morphism_map $R $Q $S $g)
        (@comm_ring_presentation_morphism_map $R $Q $S $h)
        $a
        (@comm_ring_presentation_morphism_map $R $P $Q $f));

symbol comm_ring_freyd_raw_postcomp_function_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  [g h : τ (@CommRingPresentationMorphism R Q S)]
  (a : τ (@CommRingPresentationMorphismAgreement R Q S
      (@comm_ring_presentation_morphism_map R Q S g)
      (@comm_ring_presentation_morphism_map R Q S h)))
  : τ (@= (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P S))
      (@comm_ring_freyd_raw_postcomp_function R P Q S g)
      (@comm_ring_freyd_raw_postcomp_function R P Q S h))
≔ @fapp1_fapp0
    (@Functor_cat
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R P S)))
    (@Hom_cat Grpd_cat
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P S))
    (@groupoidify_extend_func
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingFreydRawHomGroupoid R P S))
    (@comm_ring_freyd_postcomp_representation_func R P Q S g)
    (@comm_ring_freyd_postcomp_representation_func R P Q S h)
    (@comm_ring_freyd_postcomp_representation_transf R P Q S g h a);

injective symbol comm_ring_freyd_raw_comp_outer_representation_func
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R Q S)
      (Path_cat (@Function_grpd
        (@CommRingFreydRawHomGroupoid R P Q)
        (@CommRingFreydRawHomGroupoid R P S))));

rule @fapp0 _ _
      (@comm_ring_freyd_raw_comp_outer_representation_func
        $R $P $Q $S) $g
  ↪ @comm_ring_freyd_raw_postcomp_function $R $P $Q $S $g;

rule @fapp1_fapp0 _ _
      (@comm_ring_freyd_raw_comp_outer_representation_func
        $R $P $Q $S) $g $h $a
  ↪ @comm_ring_freyd_raw_postcomp_function_path
      $R $P $Q $S $g $h $a;

symbol comm_ring_freyd_raw_comp_curried
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  : τ (@Function_grpd
      (@CommRingFreydRawHomGroupoid R Q S)
      (@Function_grpd
        (@CommRingFreydRawHomGroupoid R P Q)
        (@CommRingFreydRawHomGroupoid R P S)))
≔ @groupoidify_extend_at
    (@CommRingPresentationAgreement_cat R Q S)
    (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P S))
    (@comm_ring_freyd_raw_comp_outer_representation_func R P Q S);

symbol comm_ring_freyd_raw_comp
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingFreydRawHomGroupoid R Q S))
  (f : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@CommRingFreydRawHomGroupoid R P S)
≔ (@comm_ring_freyd_raw_comp_curried R P Q S) g f;


symbol comm_ring_freyd_comp
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@CommRingFreydHomSet R P S)
≔ @trunc_rec_ambient
    trunc_zero
    (@CommRingFreydRawHomGroupoid R Q S)
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_hom_set_is_set R P S)
    (λ raw_g : τ (@CommRingFreydRawHomGroupoid R Q S),
      @trunc_map
        trunc_zero
        (@CommRingFreydRawHomGroupoid R P Q)
        (@CommRingFreydRawHomGroupoid R P S)
        (λ raw_f : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_raw_comp R P Q S raw_g raw_f)
        f)
    g;

symbol comm_ring_freyd_identity_class
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R P P)
≔ @comm_ring_freyd_hom_class R P P
    (@comm_ring_presentation_morphism_identity R P);

symbol comm_ring_freyd_zero_class
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R P Q)
≔ @comm_ring_freyd_hom_class R P Q
    (@comm_ring_presentation_morphism_zero R P Q);


injective symbol comm_ring_presentation_add_agreement_func
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingPresentationAgreement_cat R P Q));

rule @fapp0 _ _
      (@comm_ring_presentation_add_agreement_func
        $R $P $Q $f) $g
  ↪ @comm_ring_presentation_morphism_add $R $P $Q $f $g;

injective symbol comm_ring_presentation_add_agreement_fapp1
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f g g' : τ (@CommRingPresentationMorphism R P Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q g)
      (@comm_ring_presentation_morphism_map R P Q g')))
  : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_add_map R P Q f g)
      (@comm_ring_presentation_morphism_add_map R P Q f g'));

unif_rule
  @fapp1_fapp0 _ _
      (@comm_ring_presentation_add_agreement_func
        $R $P $Q $f) $g $g' $a
  ≡ @comm_ring_presentation_add_agreement_fapp1
      $R $P $Q $f $g $g' $a
  ↪ [ tt ≡ tt ];

symbol comm_ring_presentation_add_agreement_fapp1_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f g g' : τ (@CommRingPresentationMorphism R P Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q g)
      (@comm_ring_presentation_morphism_map R P Q g')))
  : τ (@= (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_add_map R P Q f g)
      (@comm_ring_presentation_morphism_add_map R P Q f g'))
      (@fapp1_fapp0
        (@CommRingPresentationAgreement_cat R P Q)
        (@CommRingPresentationAgreement_cat R P Q)
        (@comm_ring_presentation_add_agreement_func R P Q f)
        g g' a)
      (@comm_ring_presentation_add_agreement_fapp1
        R P Q f g g' a))
≔ @eq_refl
    (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_add_map R P Q f g)
      (@comm_ring_presentation_morphism_add_map R P Q f g'))
    (@fapp1_fapp0
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingPresentationAgreement_cat R P Q)
      (@comm_ring_presentation_add_agreement_func R P Q f)
      g g' a);

symbol comm_ring_freyd_add_representation_func
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R P Q)))
≔ @comp_cat_fapp0
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingPresentationAgreement_cat R P Q)
    (Path_cat (@CommRingFreydRawHomGroupoid R P Q))
    (@groupoidify_unit_func
      (@CommRingPresentationAgreement_cat R P Q))
    (@comm_ring_presentation_add_agreement_func R P Q f);

symbol comm_ring_freyd_raw_add_function
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P Q))
≔ @groupoidify_extend_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@comm_ring_freyd_add_representation_func R P Q f);

injective symbol comm_ring_freyd_add_representation_transf
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R P Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q f')))
  : τ (@Transf
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R P Q))
      (@comm_ring_freyd_add_representation_func R P Q f)
      (@comm_ring_freyd_add_representation_func R P Q f'));

rule @tapp0_fapp0 _ _ _ _ $g
      (@comm_ring_freyd_add_representation_transf
        $R $P $Q $f $f' $a)
  ↪ @comm_ring_freyd_raw_agreement_path
      $R $P $Q
      (@comm_ring_presentation_morphism_add $R $P $Q $f $g)
      (@comm_ring_presentation_morphism_add $R $P $Q $f' $g)
      (@comm_ring_presentation_agreement_add
        $R $P $Q
        (@comm_ring_presentation_morphism_map $R $P $Q $f)
        (@comm_ring_presentation_morphism_map $R $P $Q $f')
        (@comm_ring_presentation_morphism_map $R $P $Q $g)
        (@comm_ring_presentation_morphism_map $R $P $Q $g)
        $a
        (@comm_ring_presentation_agreement_refl
          $R $P $Q
          (@comm_ring_presentation_morphism_map $R $P $Q $g)));

symbol comm_ring_freyd_raw_add_function_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f f' : τ (@CommRingPresentationMorphism R P Q)]
  (a : τ (@CommRingPresentationMorphismAgreement R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q f')))
  : τ (@= (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P Q))
      (@comm_ring_freyd_raw_add_function R P Q f)
      (@comm_ring_freyd_raw_add_function R P Q f'))
≔ @fapp1_fapp0
    (@Functor_cat
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@CommRingFreydRawHomGroupoid R P Q)))
    (@Hom_cat Grpd_cat
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P Q))
    (@groupoidify_extend_func
      (@CommRingPresentationAgreement_cat R P Q)
      (@CommRingFreydRawHomGroupoid R P Q))
    (@comm_ring_freyd_add_representation_func R P Q f)
    (@comm_ring_freyd_add_representation_func R P Q f')
    (@comm_ring_freyd_add_representation_transf R P Q f f' a);

injective symbol comm_ring_freyd_raw_add_outer_representation_func
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@Functor
      (@CommRingPresentationAgreement_cat R P Q)
      (Path_cat (@Function_grpd
        (@CommRingFreydRawHomGroupoid R P Q)
        (@CommRingFreydRawHomGroupoid R P Q))));

rule @fapp0 _ _
      (@comm_ring_freyd_raw_add_outer_representation_func
        $R $P $Q) $f
  ↪ @comm_ring_freyd_raw_add_function $R $P $Q $f;

rule @fapp1_fapp0 _ _
      (@comm_ring_freyd_raw_add_outer_representation_func
        $R $P $Q) $f $f' $a
  ↪ @comm_ring_freyd_raw_add_function_path
      $R $P $Q $f $f' $a;

symbol comm_ring_freyd_raw_add_curried
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@Function_grpd
        (@CommRingFreydRawHomGroupoid R P Q)
        (@CommRingFreydRawHomGroupoid R P Q)))
≔ @groupoidify_extend_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@Function_grpd
      (@CommRingFreydRawHomGroupoid R P Q)
      (@CommRingFreydRawHomGroupoid R P Q))
    (@comm_ring_freyd_raw_add_outer_representation_func R P Q);

symbol comm_ring_freyd_raw_add
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@CommRingFreydRawHomGroupoid R P Q)
≔ (@comm_ring_freyd_raw_add_curried R P Q) f g;

symbol comm_ring_freyd_add
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingFreydHomSet R P Q))
  : τ (@CommRingFreydHomSet R P Q)
≔ @trunc_rec_ambient
    trunc_zero
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ raw_f : τ (@CommRingFreydRawHomGroupoid R P Q),
      @trunc_map
        trunc_zero
        (@CommRingFreydRawHomGroupoid R P Q)
        (@CommRingFreydRawHomGroupoid R P Q)
        (λ raw_g : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_raw_add R P Q raw_f raw_g)
        g)
    f;
