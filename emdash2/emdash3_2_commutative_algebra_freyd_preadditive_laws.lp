/*
  Full preadditive laws on arbitrary Freyd quotient-Hom points.

  The preceding class-law module proves additive and bilinearity equations on
  raw presentation classes. Set-target groupoidification extensionality first
  extends each equation to arbitrary points of the groupoidified agreement
  category. Restricted set-valued 0-truncation induction then extends it to
  arbitrary ordinary quotient-Hom points.

  Unary, binary, and ternary cases use only the corresponding generic curried
  helpers. No dependent Groupoidify eliminator, quotient representative, or
  manual coherence square is introduced here.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_preadditive_class_laws;
require open emdash.emdash3_2_groupoidification_set_extensionality;
require open emdash.emdash3_2_truncation_set_path_induction;

// Right additive unit on arbitrary raw-groupoid points after truncation.
symbol comm_ring_freyd_raw_add_zero_right_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (u : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ u)
        (@comm_ring_freyd_zero_class R P Q))
      (@trunc_intro trunc_zero _ u))
≔ @groupoidify_set_map_ext_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ u)
        (@comm_ring_freyd_zero_class R P Q))
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @trunc_intro trunc_zero _ u)
    (λ f : τ (@CommRingPresentationMorphism R P Q),
      @comm_ring_freyd_add_zero_right_class_path R P Q f)
    u;

// Right additive unit on every quotient-Hom point.
symbol comm_ring_freyd_add_zero_right_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q f
        (@comm_ring_freyd_zero_class R P Q))
      f)
≔ @trunc_zero_set_path_ind
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_add R P Q f
        (@comm_ring_freyd_zero_class R P Q))
    (λ f : τ (@CommRingFreydHomSet R P Q), f)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_raw_add_zero_right_path R P Q u)
    f;

// Left additive unit on arbitrary raw-groupoid points after truncation.
symbol comm_ring_freyd_raw_add_zero_left_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (u : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_zero_class R P Q)
        (@trunc_intro trunc_zero _ u))
      (@trunc_intro trunc_zero _ u))
≔ @groupoidify_set_map_ext_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_add R P Q
        (@comm_ring_freyd_zero_class R P Q)
        (@trunc_intro trunc_zero _ u))
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @trunc_intro trunc_zero _ u)
    (λ f : τ (@CommRingPresentationMorphism R P Q),
      @comm_ring_freyd_add_zero_left_class_path R P Q f)
    u;

// Left additive unit on every quotient-Hom point.
symbol comm_ring_freyd_add_zero_left_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_zero_class R P Q) f)
      f)
≔ @trunc_zero_set_path_ind
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_add R P Q
        (@comm_ring_freyd_zero_class R P Q) f)
    (λ f : τ (@CommRingFreydHomSet R P Q), f)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_raw_add_zero_left_path R P Q u)
    f;

// Additive associativity on arbitrary raw-groupoid triples after truncation.
symbol comm_ring_freyd_raw_add_assoc_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (u v w : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_add R P Q
          (@trunc_intro trunc_zero _ u)
          (@trunc_intro trunc_zero _ v))
        (@trunc_intro trunc_zero _ w))
      (@comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ u)
        (@comm_ring_freyd_add R P Q
          (@trunc_intro trunc_zero _ v)
          (@trunc_intro trunc_zero _ w))))
≔ @groupoidify_set_ternary_map_ext_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_add R P Q
            (@comm_ring_freyd_add R P Q
              (@trunc_intro trunc_zero _ u)
              (@trunc_intro trunc_zero _ v))
            (@trunc_intro trunc_zero _ w))
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_add R P Q
            (@trunc_intro trunc_zero _ u)
            (@comm_ring_freyd_add R P Q
              (@trunc_intro trunc_zero _ v)
              (@trunc_intro trunc_zero _ w)))
    (λ f : τ (@CommRingPresentationMorphism R P Q),
      λ g : τ (@CommRingPresentationMorphism R P Q),
        λ h : τ (@CommRingPresentationMorphism R P Q),
          @comm_ring_freyd_add_assoc_class_path R P Q f g h)
    u v w;

// Additive associativity on every quotient-Hom triple.
symbol comm_ring_freyd_add_assoc_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g h : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_add R P Q f g) h)
      (@comm_ring_freyd_add R P Q f
        (@comm_ring_freyd_add R P Q g h)))
≔ @trunc_zero_set_ternary_path_ind
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        λ h : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_add R P Q
            (@comm_ring_freyd_add R P Q f g) h)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        λ h : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_add R P Q f
            (@comm_ring_freyd_add R P Q g h))
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_raw_add_assoc_path R P Q u v w)
    f g h;

// Additive commutativity on arbitrary raw-groupoid pairs after truncation.
symbol comm_ring_freyd_raw_add_comm_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (u v : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ u)
        (@trunc_intro trunc_zero _ v))
      (@comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ v)
        (@trunc_intro trunc_zero _ u)))
≔ @groupoidify_set_binary_map_ext_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        @comm_ring_freyd_add R P Q
          (@trunc_intro trunc_zero _ u)
          (@trunc_intro trunc_zero _ v))
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        @comm_ring_freyd_add R P Q
          (@trunc_intro trunc_zero _ v)
          (@trunc_intro trunc_zero _ u))
    (λ f : τ (@CommRingPresentationMorphism R P Q),
      λ g : τ (@CommRingPresentationMorphism R P Q),
        @comm_ring_freyd_add_comm_class_path R P Q f g)
    u v;

// Additive commutativity on every quotient-Hom pair.
symbol comm_ring_freyd_add_comm_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q f g)
      (@comm_ring_freyd_add R P Q g f))
≔ @trunc_zero_set_binary_path_ind
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        @comm_ring_freyd_add R P Q f g)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        @comm_ring_freyd_add R P Q g f)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        @comm_ring_freyd_raw_add_comm_path R P Q u v)
    f g;

// Right additive inverse on arbitrary raw-groupoid points after truncation.
symbol comm_ring_freyd_raw_add_inv_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (u : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ u)
        (@comm_ring_freyd_neg R P Q
          (@trunc_intro trunc_zero _ u)))
      (@comm_ring_freyd_zero_class R P Q))
≔ @groupoidify_set_map_ext_at
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_add R P Q
        (@trunc_intro trunc_zero _ u)
        (@comm_ring_freyd_neg R P Q
          (@trunc_intro trunc_zero _ u)))
    (λ _ : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_zero_class R P Q)
    (λ f : τ (@CommRingPresentationMorphism R P Q),
      @comm_ring_freyd_add_inv_class_path R P Q f)
    u;

// Right additive inverse on every quotient-Hom point.
symbol comm_ring_freyd_add_inv_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q f
        (@comm_ring_freyd_neg R P Q f))
      (@comm_ring_freyd_zero_class R P Q))
≔ @trunc_zero_set_path_ind
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_add R P Q f
        (@comm_ring_freyd_neg R P Q f))
    (λ _ : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_zero_class R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @comm_ring_freyd_raw_add_inv_path R P Q u)
    f;

// Left inverse follows from commutativity and the selected right inverse.
symbol comm_ring_freyd_add_inv_left_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_neg R P Q f) f)
      (@comm_ring_freyd_zero_class R P Q))
≔ @eq_trans
    (@CommRingFreydHomSet R P Q)
    (@comm_ring_freyd_add R P Q
      (@comm_ring_freyd_neg R P Q f) f)
    (@comm_ring_freyd_add R P Q f
      (@comm_ring_freyd_neg R P Q f))
    (@comm_ring_freyd_zero_class R P Q)
    (@comm_ring_freyd_add_comm_path R P Q
      (@comm_ring_freyd_neg R P Q f) f)
    (@comm_ring_freyd_add_inv_path R P Q f);

// Right distributivity on arbitrary raw-groupoid triples after truncation.
symbol comm_ring_freyd_raw_comp_add_right_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (u : τ (@CommRingFreydRawHomGroupoid R Q S))
  (v w : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@trunc_intro trunc_zero _ u)
        (@comm_ring_freyd_add R P Q
          (@trunc_intro trunc_zero _ v)
          (@trunc_intro trunc_zero _ w)))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S
          (@trunc_intro trunc_zero _ u)
          (@trunc_intro trunc_zero _ v))
        (@comm_ring_freyd_comp R P Q S
          (@trunc_intro trunc_zero _ u)
          (@trunc_intro trunc_zero _ w))))
≔ @groupoidify_set_ternary_map_ext_at
    (@CommRingPresentationAgreement_cat R Q S)
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_hom_set_is_set R P S)
    (λ u : τ (@CommRingFreydRawHomGroupoid R Q S),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_comp R P Q S
            (@trunc_intro trunc_zero _ u)
            (@comm_ring_freyd_add R P Q
              (@trunc_intro trunc_zero _ v)
              (@trunc_intro trunc_zero _ w)))
    (λ u : τ (@CommRingFreydRawHomGroupoid R Q S),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_add R P S
            (@comm_ring_freyd_comp R P Q S
              (@trunc_intro trunc_zero _ u)
              (@trunc_intro trunc_zero _ v))
            (@comm_ring_freyd_comp R P Q S
              (@trunc_intro trunc_zero _ u)
              (@trunc_intro trunc_zero _ w)))
    (λ h : τ (@CommRingPresentationMorphism R Q S),
      λ f : τ (@CommRingPresentationMorphism R P Q),
        λ g : τ (@CommRingPresentationMorphism R P Q),
          @comm_ring_freyd_comp_add_right_class_path R P Q S h f g)
    u v w;

// Right distributivity on every composable quotient-Hom triple.
symbol comm_ring_freyd_comp_add_right_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (h : τ (@CommRingFreydHomSet R Q S))
  (f g : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S h
        (@comm_ring_freyd_add R P Q f g))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S h f)
        (@comm_ring_freyd_comp R P Q S h g)))
≔ @trunc_zero_set_ternary_path_ind
    (@CommRingFreydRawHomGroupoid R Q S)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_hom_set_is_set R P S)
    (λ h : τ (@CommRingFreydHomSet R Q S),
      λ f : τ (@CommRingFreydHomSet R P Q),
        λ g : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_comp R P Q S h
            (@comm_ring_freyd_add R P Q f g))
    (λ h : τ (@CommRingFreydHomSet R Q S),
      λ f : τ (@CommRingFreydHomSet R P Q),
        λ g : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_add R P S
            (@comm_ring_freyd_comp R P Q S h f)
            (@comm_ring_freyd_comp R P Q S h g))
    (λ u : τ (@CommRingFreydRawHomGroupoid R Q S),
      λ v : τ (@CommRingFreydRawHomGroupoid R P Q),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_raw_comp_add_right_path R P Q S u v w)
    h f g;

// Left distributivity on arbitrary raw-groupoid triples after truncation.
symbol comm_ring_freyd_raw_comp_add_left_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (u v : τ (@CommRingFreydRawHomGroupoid R Q S))
  (w : τ (@CommRingFreydRawHomGroupoid R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@comm_ring_freyd_add R Q S
          (@trunc_intro trunc_zero _ u)
          (@trunc_intro trunc_zero _ v))
        (@trunc_intro trunc_zero _ w))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S
          (@trunc_intro trunc_zero _ u)
          (@trunc_intro trunc_zero _ w))
        (@comm_ring_freyd_comp R P Q S
          (@trunc_intro trunc_zero _ v)
          (@trunc_intro trunc_zero _ w))))
≔ @groupoidify_set_ternary_map_ext_at
    (@CommRingPresentationAgreement_cat R Q S)
    (@CommRingPresentationAgreement_cat R Q S)
    (@CommRingPresentationAgreement_cat R P Q)
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_hom_set_is_set R P S)
    (λ u : τ (@CommRingFreydRawHomGroupoid R Q S),
      λ v : τ (@CommRingFreydRawHomGroupoid R Q S),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_comp R P Q S
            (@comm_ring_freyd_add R Q S
              (@trunc_intro trunc_zero _ u)
              (@trunc_intro trunc_zero _ v))
            (@trunc_intro trunc_zero _ w))
    (λ u : τ (@CommRingFreydRawHomGroupoid R Q S),
      λ v : τ (@CommRingFreydRawHomGroupoid R Q S),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_add R P S
            (@comm_ring_freyd_comp R P Q S
              (@trunc_intro trunc_zero _ u)
              (@trunc_intro trunc_zero _ w))
            (@comm_ring_freyd_comp R P Q S
              (@trunc_intro trunc_zero _ v)
              (@trunc_intro trunc_zero _ w)))
    (λ g : τ (@CommRingPresentationMorphism R Q S),
      λ h : τ (@CommRingPresentationMorphism R Q S),
        λ f : τ (@CommRingPresentationMorphism R P Q),
          @comm_ring_freyd_comp_add_left_class_path R P Q S g h f)
    u v w;

// Left distributivity on every composable quotient-Hom triple.
symbol comm_ring_freyd_comp_add_left_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g h : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@comm_ring_freyd_add R Q S g h) f)
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S g f)
        (@comm_ring_freyd_comp R P Q S h f)))
≔ @trunc_zero_set_ternary_path_ind
    (@CommRingFreydRawHomGroupoid R Q S)
    (@CommRingFreydRawHomGroupoid R Q S)
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_hom_set_is_set R P S)
    (λ g : τ (@CommRingFreydHomSet R Q S),
      λ h : τ (@CommRingFreydHomSet R Q S),
        λ f : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_comp R P Q S
            (@comm_ring_freyd_add R Q S g h) f)
    (λ g : τ (@CommRingFreydHomSet R Q S),
      λ h : τ (@CommRingFreydHomSet R Q S),
        λ f : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_add R P S
            (@comm_ring_freyd_comp R P Q S g f)
            (@comm_ring_freyd_comp R P Q S h f))
    (λ u : τ (@CommRingFreydRawHomGroupoid R Q S),
      λ v : τ (@CommRingFreydRawHomGroupoid R Q S),
        λ w : τ (@CommRingFreydRawHomGroupoid R P Q),
          @comm_ring_freyd_raw_comp_add_left_path R P Q S u v w)
    g h f;
