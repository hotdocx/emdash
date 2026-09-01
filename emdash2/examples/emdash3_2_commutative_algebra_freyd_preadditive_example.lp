/* Reviewer-facing full preadditivity of formal Freyd presentation categories. */

require open emdash.emdash3_2_commutative_algebra_freyd_preadditive;

// The completed construction is an honest generic preadditive structure.
assert (R : τ CommRing) ⊢
  @comm_ring_freyd_preadditive R
  : τ (@PreadditiveCategory (@CommRingFreydPresentation_cat R));

// Readable generic projections recover the selected quotient-Hom operations.
assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @preadditive_hom_zero
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R)
    P Q
  ≡ @comm_ring_freyd_zero_class R P Q;

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g : τ (@CommRingFreydHomSet R P Q)) ⊢
  @preadditive_hom_add
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R)
    P Q f g
  ≡ @comm_ring_freyd_add R P Q f g;

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingFreydHomSet R P Q)) ⊢
  @preadditive_hom_neg
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R)
    P Q f
  ≡ @comm_ring_freyd_neg R P Q f;

// Associativity now holds for arbitrary quotient points, not only raw classes.
assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  (f g h : τ (@CommRingFreydHomSet R P Q)) ⊢
  @comm_ring_freyd_add_assoc_path R P Q f g h
  : τ (@= (@CommRingFreydHomSet R P Q)
      (@comm_ring_freyd_add R P Q
        (@comm_ring_freyd_add R P Q f g) h)
      (@comm_ring_freyd_add R P Q f
        (@comm_ring_freyd_add R P Q g h)));

// Bilinearity is stated at the generic categorical composition surface.
assert (R : τ CommRing)
  (P Q S : τ (@CommRingPresentation R))
  (h : τ (@CommRingFreydHomSet R Q S))
  (f g : τ (@CommRingFreydHomSet R P Q)) ⊢
  @comm_ring_freyd_generic_comp_add_right_path R P Q S h f g
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h
        (@comm_ring_freyd_add R P Q f g))
      (@comm_ring_freyd_add R P S
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h f)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h g)));

// The package does not collapse distinct presentation categories.
assertnot (R S : τ CommRing) ⊢
  @PreadditiveCategory (@CommRingFreydPresentation_cat R)
  ≡ @PreadditiveCategory (@CommRingFreydPresentation_cat S);
