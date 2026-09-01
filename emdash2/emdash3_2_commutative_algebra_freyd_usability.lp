/*
  Lambdapi usability bridge for the formal Freyd category.

  Generic category identity/composition first meet rigid Freyd heads through
  proof-time unification, each validated by typed eq_refl. Only after those
  theorem views are declared do local runtime folds send the rigid heads to the
  already-constructed raw-class identity and quotient-Hom composition. This
  sequential order preserves the rigid discriminator during validation while
  exposing the semantic normal form afterward. Generic id/comp_fapp0 remain
  runtime owners; no rule is headed by either generic operation.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_operations;

injective symbol comm_ring_freyd_identity_head
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R P P);

unif_rule
  @id (@CommRingFreydPresentation_cat $R) $P
  ≡ @comm_ring_freyd_identity_head $R $P
  ↪ [ tt ≡ tt ];

symbol comm_ring_freyd_identity_head_path
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R P P)
      (@id (@CommRingFreydPresentation_cat R) P)
      (@comm_ring_freyd_identity_head R P))
≔ @eq_refl
    (@CommRingFreydHomSet R P P)
    (@id (@CommRingFreydPresentation_cat R) P);

// Install the semantic fold only after validating the generic/rigid bridge.
rule @comm_ring_freyd_identity_head $R $P
  ↪ @comm_ring_freyd_identity_class $R $P;

symbol comm_ring_freyd_identity_class_path
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R P P)
      (@comm_ring_freyd_identity_head R P)
      (@comm_ring_freyd_identity_class R P))
≔ @eq_refl
    (@CommRingFreydHomSet R P P)
    (@comm_ring_freyd_identity_head R P);

symbol comm_ring_freyd_identity_usability_path
  (R : τ CommRing)
  (P : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R P P)
      (@id (@CommRingFreydPresentation_cat R) P)
      (@comm_ring_freyd_identity_class R P))
≔ @eq_trans
    (@CommRingFreydHomSet R P P)
    (@id (@CommRingFreydPresentation_cat R) P)
    (@comm_ring_freyd_identity_head R P)
    (@comm_ring_freyd_identity_class R P)
    (@comm_ring_freyd_identity_head_path R P)
    (@comm_ring_freyd_identity_class_path R P);

injective symbol comm_ring_freyd_comp_head
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@CommRingFreydHomSet R P S);

unif_rule
  @comp_fapp0
      (@CommRingFreydPresentation_cat $R)
      $P $Q $S $g $f
  ≡ @comm_ring_freyd_comp_head $R $P $Q $S $g $f
  ↪ [ tt ≡ tt ];

symbol comm_ring_freyd_comp_head_path
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@comm_ring_freyd_comp_head R P Q S g f))
≔ @eq_refl
    (@CommRingFreydHomSet R P S)
    (@comp_fapp0
      (@CommRingFreydPresentation_cat R)
      P Q S g f);

// Install the transparent descent fold after the generic/rigid proof.
rule @comm_ring_freyd_comp_head $R $P $Q $S $g $f
  ↪ @comm_ring_freyd_comp $R $P $Q $S $g $f;

symbol comm_ring_freyd_comp_semantic_path
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp_head R P Q S g f)
      (@comm_ring_freyd_comp R P Q S g f))
≔ @eq_refl
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_comp_head R P Q S g f);

symbol comm_ring_freyd_comp_usability_path
  (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (g : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@comm_ring_freyd_comp R P Q S g f))
≔ @eq_trans
    (@CommRingFreydHomSet R P S)
    (@comp_fapp0
      (@CommRingFreydPresentation_cat R)
      P Q S g f)
    (@comm_ring_freyd_comp_head R P Q S g f)
    (@comm_ring_freyd_comp R P Q S g f)
    (@comm_ring_freyd_comp_head_path R P Q S g f)
    (@comm_ring_freyd_comp_semantic_path R P Q S g f);
