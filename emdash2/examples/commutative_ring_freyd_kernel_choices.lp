/* Reviewer: retained universal operations, literal ranks and matrix projections. */

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choices;

// Both retained selections have ordinary constructor beta, without equality casts.
assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (U : τ (@CommRingFreydKernelFirstChoice R P Q f))
  (V : τ (@CommRingFreydKernelSecondChoice R P Q f U))
  ⊢ @comm_ring_freyd_kernel_choices_first R P Q f
      (@comm_ring_freyd_kernel_choices_intro R P Q f U V) ≡ U;

assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (U : τ (@CommRingFreydKernelFirstChoice R P Q f))
  (V : τ (@CommRingFreydKernelSecondChoice R P Q f U))
  ⊢ @comm_ring_freyd_kernel_choices_second R P Q f
      (@comm_ring_freyd_kernel_choices_intro R P Q f U V) ≡ V;

// Arbitrary annihilated-test factors are retained, not replaced by sample matrices.
assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (K : τ (@CommRingFreydKernelChoices R P Q f)) (n : τ Nat_grpd)
  (cone : τ (@WeakPullbackCone
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q) n))
  ⊢ @computational_weak_pullback_lift
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R)
    (@comm_ring_presentation_generators R P)
    (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f)
    (@comm_ring_presentation_matrix R Q)
    (@comm_ring_freyd_kernel_choices_first R P Q f K) n cone
  : τ (@CommRingMatrix R (@comm_ring_freyd_selected_kernel_rank R P Q f K) n);

assert (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (cone : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b k))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k cone factor))
  ⊢ @comm_ring_finite_free_weak_pullback_rank R x y z a b
    (@comm_ring_finite_free_weak_pullback_intro R x y z a b k cone factor law) ≡ k;

// Selecting a literal rank does not collapse it to the zero object.
assertnot (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (cone : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b k))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k cone factor))
  ⊢ @comm_ring_finite_free_weak_pullback_rank R x y z a b
    (@comm_ring_finite_free_weak_pullback_intro R x y z a b k cone factor law) ≡ zero;

// The dependent second choice cannot be silently reused at another first choice.
assertnot (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q))
  (U U_other : τ (@CommRingFreydKernelFirstChoice R P Q f))
  (V : τ (@CommRingFreydKernelSecondChoice R P Q f U))
  ⊢ V : τ (@CommRingFreydKernelSecondChoice R P Q f U_other);

assert (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comp_fapp0 (@CommRingFiniteFree_cat R) k x y a p)
    (@comp_fapp0 (@CommRingFiniteFree_cat R) k z y b q)))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_pair_cone R x y z k a b p q compatible) factor))
  ⊢ @comm_ring_finite_free_weak_pullback_proj1 R x y z a b
    (@comm_ring_finite_free_weak_pullback_intro R x y z a b k
      (@comm_ring_finite_free_weak_pullback_pair_cone R x y z k a b p q compatible) factor law)
    ≡ p;

// A dependent consumer instantiates both choices at explicit ranks.
assert (R : τ CommRing) (P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R P Q)) (k1 k2 : τ Nat_grpd)
  (cone1 : τ (@CommRingFiniteFreeWeakPullbackCone R
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1))
  (factor1 : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1))
  (law1 : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
    (@comm_ring_presentation_relations R Q)
    (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1 cone1 factor1))
  (cone2 : τ (@CommRingFiniteFreeWeakPullbackCone R k1
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_relations R P)
    (@weak_pullback_cone_proj1 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1 cone1)
    (@comm_ring_presentation_matrix R P) k2))
  (factor2 : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R k1
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_relations R P)
    (@weak_pullback_cone_proj1 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1 cone1)
    (@comm_ring_presentation_matrix R P) k2))
  (law2 : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R k1
    (@comm_ring_presentation_generators R P) (@comm_ring_presentation_relations R P)
    (@weak_pullback_cone_proj1 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero (@comm_ring_finite_free_additive R)
      (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
      (@comm_ring_presentation_relations R Q)
      (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1 cone1)
    (@comm_ring_presentation_matrix R P) k2 cone2 factor2))
  ⊢ @comm_ring_freyd_selected_kernel_relation_matrix R P Q f
    (@comm_ring_freyd_kernel_choices_intro R P Q f
      (@comm_ring_finite_free_weak_pullback_intro R
        (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
        (@comm_ring_presentation_relations R Q)
        (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q)
        k1 cone1 factor1 law1)
      (@comm_ring_finite_free_weak_pullback_intro R k1
        (@comm_ring_presentation_generators R P) (@comm_ring_presentation_relations R P)
        (@weak_pullback_cone_proj1 (@CommRingFiniteFree_cat R)
          (@comm_ring_finite_free_direct_sum_func R) zero (@comm_ring_finite_free_additive R)
          (@comm_ring_presentation_generators R P) (@comm_ring_presentation_generators R Q)
          (@comm_ring_presentation_relations R Q)
          (@comm_ring_presentation_morphism_map R P Q f) (@comm_ring_presentation_matrix R Q) k1 cone1)
        (@comm_ring_presentation_matrix R P) k2 cone2 factor2 law2))
  : τ (@CommRingMatrix R k1 k2);
