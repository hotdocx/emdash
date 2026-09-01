/*
  The zero presentation as a selected terminal object in the formal Freyd
  category.

  A matrix with zero target rows is uniquely zero. That constructive fact
  turns every raw map into the zero presentation into an agreement with the
  zero map, then the established groupoidification and set-truncation ladder
  extends the equality to arbitrary quotient-Hom points. No representative
  choice, manual commuting square, or opaque uniqueness witness is used.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_binary_products;
require open emdash.emdash3_2_commutative_algebra_matrix_zero_rows;
require open emdash.emdash3_2_terminal_objects;

// A raw map into the zero presentation agrees with the zero map.
symbol comm_ring_freyd_to_zero_class_path
  [R : τ CommRing]
  [P : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P
      (@comm_ring_zero_presentation R)))
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R))
      (@comm_ring_freyd_hom_class R P
        (@comm_ring_zero_presentation R) f)
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R)))
≔ @comm_ring_freyd_agreement_path R P
    (@comm_ring_zero_presentation R)
    f
    (@comm_ring_presentation_morphism_zero R P
      (@comm_ring_zero_presentation R))
    (@comm_ring_presentation_agreement_of_map_path R P
      (@comm_ring_zero_presentation R)
      (@comm_ring_presentation_morphism_map R P
        (@comm_ring_zero_presentation R) f)
      (@comm_ring_presentation_morphism_map R P
        (@comm_ring_zero_presentation R)
        (@comm_ring_presentation_morphism_zero R P
          (@comm_ring_zero_presentation R)))
      (@comm_ring_matrix_zero_rows_path R
        (@comm_ring_presentation_generators R P)
        (@comm_ring_presentation_morphism_map R P
          (@comm_ring_zero_presentation R) f)));

// The same equality on every groupoidified raw-Hom point.
symbol comm_ring_freyd_raw_to_zero_path
  [R : τ CommRing]
  [P : τ (@CommRingPresentation R)]
  (u : τ (@CommRingFreydRawHomGroupoid R P
      (@comm_ring_zero_presentation R)))
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R))
      (@trunc_intro trunc_zero _ u)
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R)))
≔ @groupoidify_set_map_ext_at
    (@CommRingPresentationAgreement_cat R P
      (@comm_ring_zero_presentation R))
    (@CommRingFreydHomSet R P (@comm_ring_zero_presentation R))
    (@comm_ring_freyd_hom_set_is_set R P
      (@comm_ring_zero_presentation R))
    (λ v : τ (@CommRingFreydRawHomGroupoid R P
        (@comm_ring_zero_presentation R)),
      @trunc_intro trunc_zero _ v)
    (λ _ : τ (@CommRingFreydRawHomGroupoid R P
        (@comm_ring_zero_presentation R)),
      @comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R))
    (λ f : τ (@CommRingPresentationMorphism R P
        (@comm_ring_zero_presentation R)),
      @comm_ring_freyd_to_zero_class_path R P f)
    u;

// Every quotient-Hom point into zero is the zero arrow.
symbol comm_ring_freyd_to_zero_path
  [R : τ CommRing]
  [P : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R)))
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R))
      f
      (@comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R)))
≔ @trunc_zero_set_path_ind
    (@CommRingFreydRawHomGroupoid R P
      (@comm_ring_zero_presentation R))
    (@CommRingFreydHomSet R P (@comm_ring_zero_presentation R))
    (@comm_ring_freyd_hom_set_is_set R P
      (@comm_ring_zero_presentation R))
    (λ f0 : τ (@CommRingFreydHomSet R P
        (@comm_ring_zero_presentation R)), f0)
    (λ _ : τ (@CommRingFreydHomSet R P
        (@comm_ring_zero_presentation R)),
      @comm_ring_freyd_zero_class R P
        (@comm_ring_zero_presentation R))
    (λ u : τ (@CommRingFreydRawHomGroupoid R P
        (@comm_ring_zero_presentation R)),
      @comm_ring_freyd_raw_to_zero_path R P u)
    f;

// Contractibility is recentered at the selected zero arrow.
symbol comm_ring_freyd_zero_terminal_hom_contr
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (IsContr (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R)))
≔ @Struct_sigma
    (@CommRingFreydHomSet R P (@comm_ring_zero_presentation R))
    (λ centre : τ _, @Pi_grpd _ (λ f : τ _, @= _ centre f))
    (@comm_ring_freyd_zero_class R P (@comm_ring_zero_presentation R))
    (λ f : τ (@CommRingFreydHomSet R P
        (@comm_ring_zero_presentation R)),
      @eq_sym
        (@CommRingFreydHomSet R P (@comm_ring_zero_presentation R))
        f
        (@comm_ring_freyd_zero_class R P
          (@comm_ring_zero_presentation R))
        (@comm_ring_freyd_to_zero_path R P f));

// Selected terminal-object witness at the zero presentation.
injective symbol comm_ring_freyd_terminal_zero
  (R : τ CommRing)
  : τ (@TerminalObject
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R));

injective symbol comm_ring_freyd_terminal_zero_arrow
  [R : τ CommRing]
  (P : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R P (@comm_ring_zero_presentation R));

// Proof-time usability comparison preserves the generic terminal-arrow head.
unif_rule
  @terminal_arrow_fapp0
      _ _ (@comm_ring_freyd_terminal_zero $R) $P
  ≡ @comm_ring_freyd_terminal_zero_arrow $R $P
  ↪ [ tt ≡ tt ];

symbol comm_ring_freyd_terminal_zero_arrow_path
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R P
      (@comm_ring_zero_presentation R))
      (@terminal_arrow_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R)
        (@comm_ring_freyd_terminal_zero R) P)
      (@comm_ring_freyd_terminal_zero_arrow R P))
≔ @eq_refl _
    (@terminal_arrow_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R)
      (@comm_ring_freyd_terminal_zero R) P);

rule @comm_ring_freyd_terminal_zero_arrow $R $P
  ↪ @comm_ring_freyd_zero_class $R $P
      (@comm_ring_zero_presentation $R);

// The semantic contractibility observation exposes the constructed descent.
rule @terminal_hom_contr
      _ _ (@comm_ring_freyd_terminal_zero $R) $P
  ↪ @comm_ring_freyd_zero_terminal_hom_contr $R $P;
