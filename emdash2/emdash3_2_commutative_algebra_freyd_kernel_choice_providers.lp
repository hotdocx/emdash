/*
  Literal-matrix provider data for the existing selected weak-pullback owners.

  Compatibility is a matrix equation. The provider supplies an all-test
  factor operation and its reconstruction law at the original paired cone;
  neither operation is inferred from finite replay. Transparent introductions
  expose literal indices to a signature-only frontend and return the existing
  universal packages. No global weak-kernel selector, cast, or axiom is added.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choices;
require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;

// Matrix compatibility reads as the generic finite-free composition equation.
symbol comm_ring_finite_free_weak_pullback_matrix_compatibility_to_generic
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  : τ (@= (@CommRingMatrix R y k)
    (@comp_fapp0 (@CommRingFiniteFree_cat R) k x y a p)
    (@comp_fapp0 (@CommRingFiniteFree_cat R) k z y b q))
≔ @eq_trans _ _ (@comm_ring_matrix_comp R y x k a p) _
    (@comm_ring_finite_free_comp_fapp0_transparent_path R k x y a p)
    (@eq_trans _ _ (@comm_ring_matrix_comp R y z k b q) _ compatible
      (@eq_sym _ _ _ (@comm_ring_finite_free_comp_fapp0_transparent_path R k z y b q)));

// The literal pair enters the existing internal annihilator cone.
symbol comm_ring_finite_free_weak_pullback_cone_from_matrices
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b k)
≔ @comm_ring_finite_free_weak_pullback_pair_cone R x y z k a b p q
    (@comm_ring_finite_free_weak_pullback_matrix_compatibility_to_generic
      R x y z k a b p q compatible);

// Actual all-test operation/law at a fixed literal candidate rank and pair.
symbol CommRingFiniteFreeWeakPullbackMatrixProvider
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  : Grpd
≔ `Σ_ factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k),
   (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible) factor);

symbol comm_ring_finite_free_weak_pullback_matrix_provider_intro
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible) factor))
  : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible)
≔ @Struct_sigma (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k)
    (λ selected : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k), (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible) selected))
    factor law;

// Retain the exact supplied operation, including tests absent from finite replay.
symbol comm_ring_finite_free_weak_pullback_matrix_provider_factor
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k)
≔ sigma_Fst provider;

symbol comm_ring_finite_free_weak_pullback_matrix_provider_law
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible) (@comm_ring_finite_free_weak_pullback_matrix_provider_factor
      R x y z k a b p q compatible provider))
≔ sigma_Snd provider;

// The result is the original whole weak pullback at the supplied literal data.
symbol comm_ring_finite_free_weak_pullback_from_matrix_provider
  (R : τ CommRing) (x y z k : τ Nat_grpd)
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comm_ring_matrix_comp R y x k a p)
    (@comm_ring_matrix_comp R y z k b q)))
  (provider : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider R x y z k a b p q compatible))
  : τ (@CommRingFiniteFreeWeakPullback R x y z a b)
≔ @comm_ring_finite_free_weak_pullback_intro R x y z a b k
    (@comm_ring_finite_free_weak_pullback_cone_from_matrices R x y z k a b p q compatible)
    (@comm_ring_finite_free_weak_pullback_matrix_provider_factor
      R x y z k a b p q compatible provider)
    (@comm_ring_finite_free_weak_pullback_matrix_provider_law
      R x y z k a b p q compatible provider);

// Both literal providers construct choices for the original explicit-data f.
// The second cospan is literally p1,R_P; first-constructor beta supplies its type.
symbol comm_ring_freyd_kernel_choices_from_matrix_providers
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
  : τ (@CommRingFreydKernelChoices R
    (@comm_ring_presentation_intro R p pr P)
    (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_presentation_morphism_from_matrices R p pr q qr P Q F WF lawF))
≔ @comm_ring_freyd_kernel_choices_intro R
    (@comm_ring_presentation_intro R p pr P)
    (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_presentation_morphism_from_matrices R p pr q qr P Q F WF lawF)
    (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R p q qr k1 F Q p1 q1 compatible1 provider1)
    (@comm_ring_finite_free_weak_pullback_from_matrix_provider
      R k1 p pr k2 p1 P p2 q2 compatible2 provider2);
