/* Reviewer-facing preadditive laws on raw Freyd classes. */

require open emdash.emdash3_2_commutative_algebra_freyd_preadditive_class_laws;

symbol freyd_class_add_assoc_reviewer_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f g h : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_add R P Q
          (@comm_ring_freyd_hom_class R P Q f)
          (@comm_ring_freyd_hom_class R P Q g))
        (@comm_ring_freyd_hom_class R P Q h))
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_add R P Q
          (@comm_ring_freyd_hom_class R P Q g)
          (@comm_ring_freyd_hom_class R P Q h))))
≔ @comm_ring_freyd_add_assoc_class_path R P Q f g h;

symbol freyd_class_add_inverse_reviewer_path
  [R : τ CommRing]
  [P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_hom_class R P Q f)
        (@comm_ring_freyd_neg R P Q
          (@comm_ring_freyd_hom_class R P Q f)))
      (@comm_ring_freyd_zero_class R P Q))
≔ @comm_ring_freyd_add_inv_class_path R P Q f;

symbol freyd_class_right_distrib_reviewer_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (h : τ (@CommRingPresentationMorphism R Q S))
  (f g : τ (@CommRingPresentationMorphism R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@comm_ring_freyd_hom_class R Q S h)
        (@comm_ring_freyd_add R P Q
          (@comm_ring_freyd_hom_class R P Q f)
          (@comm_ring_freyd_hom_class R P Q g)))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S
          (@comm_ring_freyd_hom_class R Q S h)
          (@comm_ring_freyd_hom_class R P Q f))
        (@comm_ring_freyd_comp R P Q S
          (@comm_ring_freyd_hom_class R Q S h)
          (@comm_ring_freyd_hom_class R P Q g))))
≔ @comm_ring_freyd_comp_add_right_class_path R P Q S h f g;

assertnot
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingFreydHomSet R P Q))
  ⊢ @comm_ring_freyd_neg R P Q f
  ≡ g;
