/*
  Reviewer: literal providers retain ranks, projections, universal operations,
  laws and the dependent second choice. Wrong rank/choice assertions remain
  negative rather than coercing a different provider into the selected owner.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choice_providers;

assert
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  ⊢ @comm_ring_finite_free_weak_pullback_rank R x y z a b (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R x y z k a b p q compatible provider) ≡ k;

assert
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  ⊢ @comm_ring_finite_free_weak_pullback_proj1 R x y z a b (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R x y z k a b p q compatible provider) ≡ p;

assert
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  ⊢ @comm_ring_finite_free_weak_pullback_proj2 R x y z a b (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R x y z k a b p q compatible provider) ≡ q;

// Both fields are the actual supplied all-test operation and law.
assert
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible) factor))
  ⊢ @comm_ring_finite_free_weak_pullback_matrix_provider_factor
    R x y z k a b p q compatible (@comm_ring_finite_free_weak_pullback_matrix_provider_intro
      R x y z k a b p q compatible factor law) ≡ factor;

assert
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible) factor))
  ⊢ @comm_ring_finite_free_weak_pullback_matrix_provider_law
    R x y z k a b p q compatible (@comm_ring_finite_free_weak_pullback_matrix_provider_intro
      R x y z k a b p q compatible factor law) ≡ law;

// A fresh arbitrary test is handled by the retained provider operation.
assert
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  (n : τ Nat_grpd)
  (test : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b n))
  ⊢ @computational_weak_pullback_lift
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_direct_sum_func R)
    zero (@comm_ring_finite_free_additive R) x y z a b (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R x y z k a b p q compatible provider) n test
    ≡ (@comm_ring_finite_free_weak_pullback_matrix_provider_factor
      R x y z k a b p q compatible provider) n test;

// The resulting presentation keeps the two literal ranks and relation matrix.
assert
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F : τ (@CommRingMatrix R q p)) (WF : τ (@CommRingMatrix R qr pr))
  (lawF : τ (@= (@CommRingMatrix R q pr)
    (@comm_ring_matrix_comp R q qr pr Q WF)
    (@comm_ring_matrix_comp R q p pr F P)))
  (k1 : τ Nat_grpd)
  (p1 : τ (@CommRingMatrix R p k1)) (q1 : τ (@CommRingMatrix R qr k1))
  (compatible1 : τ (@= (@CommRingMatrix R q k1)
    (@comm_ring_matrix_comp R q p k1 F p1)
    (@comm_ring_matrix_comp R q qr k1 Q q1)))
  (provider1 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R p q qr k1 F Q p1 q1 compatible1))
  (k2 : τ Nat_grpd)
  (p2 : τ (@CommRingMatrix R k1 k2)) (q2 : τ (@CommRingMatrix R pr k2))
  (compatible2 : τ (@= (@CommRingMatrix R p k2)
    (@comm_ring_matrix_comp R p k1 k2 p1 p2)
    (@comm_ring_matrix_comp R p pr k2 P q2)))
  (provider2 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 p pr k2 p1 P p2 q2 compatible2))
  ⊢ @comm_ring_freyd_selected_kernel_presentation R (@comm_ring_presentation_intro R p pr P) (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_presentation_morphism_from_matrices R p pr q qr P Q F WF lawF)
    (@comm_ring_freyd_kernel_choices_from_matrix_providers R p pr q qr P Q F WF lawF
      k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2)
    ≡ @comm_ring_presentation_intro R k1 k2 p2;

assert
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F : τ (@CommRingMatrix R q p)) (WF : τ (@CommRingMatrix R qr pr))
  (lawF : τ (@= (@CommRingMatrix R q pr)
    (@comm_ring_matrix_comp R q qr pr Q WF)
    (@comm_ring_matrix_comp R q p pr F P)))
  (k1 : τ Nat_grpd)
  (p1 : τ (@CommRingMatrix R p k1)) (q1 : τ (@CommRingMatrix R qr k1))
  (compatible1 : τ (@= (@CommRingMatrix R q k1)
    (@comm_ring_matrix_comp R q p k1 F p1)
    (@comm_ring_matrix_comp R q qr k1 Q q1)))
  (provider1 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R p q qr k1 F Q p1 q1 compatible1))
  (k2 : τ Nat_grpd)
  (p2 : τ (@CommRingMatrix R k1 k2)) (q2 : τ (@CommRingMatrix R pr k2))
  (compatible2 : τ (@= (@CommRingMatrix R p k2)
    (@comm_ring_matrix_comp R p k1 k2 p1 p2)
    (@comm_ring_matrix_comp R p pr k2 P q2)))
  (provider2 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 p pr k2 p1 P p2 q2 compatible2))
  ⊢ @comm_ring_freyd_selected_kernel_projection R (@comm_ring_presentation_intro R p pr P) (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_presentation_morphism_from_matrices R p pr q qr P Q F WF lawF)
    (@comm_ring_freyd_kernel_choices_from_matrix_providers R p pr q qr P Q F WF lawF
      k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2) ≡ p1;

// The actual retained second package is built at the literal cospan p1,P.
assert
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F : τ (@CommRingMatrix R q p)) (WF : τ (@CommRingMatrix R qr pr))
  (lawF : τ (@= (@CommRingMatrix R q pr)
    (@comm_ring_matrix_comp R q qr pr Q WF)
    (@comm_ring_matrix_comp R q p pr F P)))
  (k1 : τ Nat_grpd)
  (p1 : τ (@CommRingMatrix R p k1)) (q1 : τ (@CommRingMatrix R qr k1))
  (compatible1 : τ (@= (@CommRingMatrix R q k1)
    (@comm_ring_matrix_comp R q p k1 F p1)
    (@comm_ring_matrix_comp R q qr k1 Q q1)))
  (provider1 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R p q qr k1 F Q p1 q1 compatible1))
  (k2 : τ Nat_grpd)
  (p2 : τ (@CommRingMatrix R k1 k2)) (q2 : τ (@CommRingMatrix R pr k2))
  (compatible2 : τ (@= (@CommRingMatrix R p k2)
    (@comm_ring_matrix_comp R p k1 k2 p1 p2)
    (@comm_ring_matrix_comp R p pr k2 P q2)))
  (provider2 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 p pr k2 p1 P p2 q2 compatible2))
  ⊢ @comm_ring_freyd_kernel_choices_second R (@comm_ring_presentation_intro R p pr P) (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_presentation_morphism_from_matrices R p pr q qr P Q F WF lawF)
    (@comm_ring_freyd_kernel_choices_from_matrix_providers R p pr q qr P Q F WF lawF
      k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2)
    ≡ @comm_ring_finite_free_weak_pullback_from_matrix_provider
      R k1 p pr k2 p1 P p2 q2 compatible2 provider2;

// A supplied rank does not collapse to a different literal.
assertnot
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  ⊢ @comm_ring_finite_free_weak_pullback_rank R x y z a b (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R x y z k a b p q compatible provider) ≡ succ k;

// Same dimensions do not permit a provider for a different second cospan.
assertnot
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F : τ (@CommRingMatrix R q p)) (WF : τ (@CommRingMatrix R qr pr))
  (lawF : τ (@= (@CommRingMatrix R q pr)
    (@comm_ring_matrix_comp R q qr pr Q WF)
    (@comm_ring_matrix_comp R q p pr F P)))
  (k1 : τ Nat_grpd)
  (p1 : τ (@CommRingMatrix R p k1)) (q1 : τ (@CommRingMatrix R qr k1))
  (compatible1 : τ (@= (@CommRingMatrix R q k1)
    (@comm_ring_matrix_comp R q p k1 F p1)
    (@comm_ring_matrix_comp R q qr k1 Q q1)))
  (provider1 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R p q qr k1 F Q p1 q1 compatible1))
  (k2 : τ Nat_grpd)
  (p2 : τ (@CommRingMatrix R k1 k2)) (q2 : τ (@CommRingMatrix R pr k2))
  (compatible2 : τ (@= (@CommRingMatrix R p k2)
    (@comm_ring_matrix_comp R p k1 k2 p1 p2)
    (@comm_ring_matrix_comp R p pr k2 P q2)))
  (provider2 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 p pr k2 p1 P p2 q2 compatible2))
  (other : τ (@CommRingMatrix R p k1))
  (otherCompatible : τ (@= (@CommRingMatrix R p k2)
    (@comm_ring_matrix_comp R p k1 k2 other p2)
    (@comm_ring_matrix_comp R p pr k2 P q2)))
  (otherProvider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 p pr k2 other P p2 q2 otherCompatible))
  ⊢ @comm_ring_freyd_kernel_choices_from_matrix_providers R p pr q qr P Q F WF lawF
    k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 otherProvider
  : τ (@CommRingFreydKernelChoices R (@comm_ring_presentation_intro R p pr P) (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_presentation_morphism_from_matrices R p pr q qr P Q F WF lawF));
