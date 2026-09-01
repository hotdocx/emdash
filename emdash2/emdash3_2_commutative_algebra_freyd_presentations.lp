/*
  Homwise quotient semantics and the formal Freyd presentation category.

  For fixed presentations P,Q, raw relation-preserving morphisms are objects of
  an agreement category and target-factorization witnesses are its arrows.
  Generic category-indexed groupoidification retains that higher agreement;
  0-truncation yields the ordinary quotient Hom set. The Freyd category uses
  these quotient Homs, and elements are represented by Hom from the relation-
  free rank-one presentation. Generic Freyd identity/composition remain
  category owners; their explicit class-level descent is separately gated.
*/

require open emdash.emdash3_2_commutative_algebra_presentation_operations;
require open emdash.emdash3_2_groupoidification_universality;
require open emdash.emdash3_2_truncation_reflector;

// Raw morphisms and representative-agreement witnesses at fixed endpoints.
injective symbol CommRingPresentationAgreement_cat
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : Cat;

rule Obj (@CommRingPresentationAgreement_cat $R $P $Q)
  ↪ @CommRingPresentationMorphism $R $P $Q;

rule Hom_cat
      (@CommRingPresentationAgreement_cat $R $P $Q) $f $g
  ↪ Path_cat
      (@CommRingPresentationMorphismAgreement
        $R $P $Q
        (@comm_ring_presentation_morphism_map $R $P $Q $f)
        (@comm_ring_presentation_morphism_map $R $P $Q $g));

// Higher quotient retaining agreement witnesses and their syzygy paths.
symbol CommRingFreydRawHomGroupoid
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : Grpd
≔ @Groupoidify (@CommRingPresentationAgreement_cat R P Q);

// Ordinary quotient Hom carrier: equality is proposition-valued.
symbol CommRingFreydHomSet
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : Grpd
≔ @Trunc_grpd trunc_zero (@CommRingFreydRawHomGroupoid R P Q);

symbol comm_ring_freyd_hom_set_is_set
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (IsSetGrpd (@CommRingFreydHomSet R P Q))
≔ @trunc_ntype_is_truncated
    trunc_zero (@CommRingFreydRawHomGroupoid R P Q);

// Class of one raw presentation morphism in the untruncated Hom groupoid.
symbol comm_ring_freyd_raw_groupoid_class
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydRawHomGroupoid R P Q)
≔ @fapp0
    (@CommRingPresentationAgreement_cat R P Q)
    (Path_cat (@CommRingFreydRawHomGroupoid R P Q))
    (@groupoidify_unit_func
      (@CommRingPresentationAgreement_cat R P Q))
    f;

// Class in the ordinary 0-truncated quotient Hom.
symbol comm_ring_freyd_hom_class
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@CommRingFreydHomSet R P Q)
≔ @trunc_intro
    trunc_zero (@CommRingFreydRawHomGroupoid R P Q)
    (@comm_ring_freyd_raw_groupoid_class R P Q f);

// One agreement witness becomes a path between untruncated raw classes.
symbol comm_ring_freyd_raw_agreement_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f g : τ (@CommRingPresentationMorphism R P Q)]
  (agreement : τ (@CommRingPresentationMorphismAgreement
      R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g)))
  : τ (@= (@CommRingFreydRawHomGroupoid R P Q)
      (@comm_ring_freyd_raw_groupoid_class R P Q f)
      (@comm_ring_freyd_raw_groupoid_class R P Q g))
≔ @fapp1_fapp0
    (@CommRingPresentationAgreement_cat R P Q)
    (Path_cat (@CommRingFreydRawHomGroupoid R P Q))
    (@groupoidify_unit_func
      (@CommRingPresentationAgreement_cat R P Q))
    f g agreement;

// The same agreement yields ordinary equality after 0-truncation.
symbol comm_ring_freyd_agreement_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  [f g : τ (@CommRingPresentationMorphism R P Q)]
  (agreement : τ (@CommRingPresentationMorphismAgreement
      R P Q
      (@comm_ring_presentation_morphism_map R P Q f)
      (@comm_ring_presentation_morphism_map R P Q g)))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_hom_class R P Q f)
      (@comm_ring_freyd_hom_class R P Q g))
≔ @eq_ap
    (@CommRingFreydRawHomGroupoid R P Q)
    (@CommRingFreydHomSet R P Q)
    (λ u : τ (@CommRingFreydRawHomGroupoid R P Q),
      @trunc_intro trunc_zero
        (@CommRingFreydRawHomGroupoid R P Q) u)
    (@comm_ring_freyd_raw_groupoid_class R P Q f)
    (@comm_ring_freyd_raw_groupoid_class R P Q g)
    (@comm_ring_freyd_raw_agreement_path R P Q f g agreement);

// Formal category of presentations with quotient Hom sets.
injective symbol CommRingFreydPresentation_cat
  (R : τ CommRing)
  : Cat;

rule Obj (@CommRingFreydPresentation_cat $R)
  ↪ @CommRingPresentation $R;

rule Hom_cat (@CommRingFreydPresentation_cat $R) $P $Q
  ↪ Path_cat (@CommRingFreydHomSet $R $P $Q);

// Relation-free rank-one presentation representing ordinary elements.
symbol comm_ring_free_one_presentation
  (R : τ CommRing)
  : τ (@CommRingPresentation R)
≔ @comm_ring_presentation_intro R
    (succ zero) zero
    (@comm_ring_matrix_zero R (succ zero) zero);

// Ordinary element carrier derived representably from the Freyd Hom.
symbol CommRingFreydElement
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : Grpd
≔ @CommRingFreydHomSet R
    (@comm_ring_free_one_presentation R) P;

// Class of any raw map from FreeOne; direct vector construction is later.
symbol comm_ring_freyd_element_of_raw
  [R : τ CommRing]
  [P : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R
      (@comm_ring_free_one_presentation R) P))
  : τ (@CommRingFreydElement R P)
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_free_one_presentation R) P f;

symbol comm_ring_freyd_element_agreement_path
  [R : τ CommRing]
  [P : τ (@CommRingPresentation R)]
  [f g : τ (@CommRingPresentationMorphism R
      (@comm_ring_free_one_presentation R) P)]
  (agreement : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_free_one_presentation R) P
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_free_one_presentation R) P f)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_free_one_presentation R) P g)))
  : τ (@= (@CommRingFreydElement R P)
      (@comm_ring_freyd_element_of_raw R P f)
      (@comm_ring_freyd_element_of_raw R P g))
≔ @comm_ring_freyd_agreement_path R
    (@comm_ring_free_one_presentation R) P f g agreement;
