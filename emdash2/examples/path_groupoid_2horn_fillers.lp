/*
  Focused reviewer for algebraic two-horn fillers in a path groupoid.

  Presheaf-facing restriction remains ordinary precomposition by the selected
  horn inclusion. The bounded strict-nerve carrier computes inner filling by
  composition and outer filling by inverses. J-derived cancellation proves
  all three section laws, and Path-map lifting retains higher action.
*/

require open emdash.emdash3_2_path_groupoid_2horn_fillers;

// Generic partial-simplex restriction is the existing whole precomposition.
assert
  (kind : τ Simplex2SieveKind)
  (X : τ (@Psh SemiDeltaPlus_cat)) ⊢
  @simplex2_partial_restrict kind X
  : τ (Functor
      (Hom_cat
        (@Psh_cat SemiDeltaPlus_cat)
        (@StandardSimplex (succ (succ (succ zero))))
        X)
      (Hom_cat
        (@Psh_cat SemiDeltaPlus_cat)
        (@simplex2_sieve_extension_psh kind)
        X));

// The right-J composition has its intended conventional path reading.
assert
  [G : Grpd]
  [x y z : τ G]
  (p : τ (@= G x y))
  (q : τ (@= G y z)) ⊢
  @eq_trans_right_agrees G x y z p q
  : τ (@=
      (@= G x z)
      (@eq_trans_right G x y z p q)
      (@eq_trans G x y z p q));

// Inner-horn filling is literal path composition.
assert
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p01 : τ (@= G x0 x1))
  (p12 : τ (@= G x1 x2)) ⊢
  @path_nerve2_simplex_p02
    G
    (@path_nerve2_fill_one G
      (@path_nerve2_simplex_intro G x0 x1 x2 p01 p12))
  ≡ @eq_trans G x0 x1 x2 p01 p12;

// Horn 0 solves edge 12 by p01^-1 followed by p02.
assert
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p01 : τ (@= G x0 x1))
  (p02 : τ (@= G x0 x2)) ⊢
  @path_nerve2_simplex_p12
    G
    (@path_nerve2_fill_zero G
      (@path_nerve2_horn_zero_intro G x0 x1 x2 p01 p02))
  ≡ @eq_trans G x1 x0 x2 (@eq_sym G x0 x1 p01) p02;

// Horn 2 solves edge 01 by p02 followed by p12^-1.
assert
  [G : Grpd]
  (x0 x1 x2 : τ G)
  (p02 : τ (@= G x0 x2))
  (p12 : τ (@= G x1 x2)) ⊢
  @path_nerve2_simplex_p01
    G
    (@path_nerve2_fill_two G
      (@path_nerve2_horn_two_intro G x0 x1 x2 p02 p12))
  ≡ @eq_trans_right
      G x0 x2 x1 p02 (@eq_sym G x1 x2 p12);

// The two outer cancellation lemmas are internally J-derived.
assert
  [G : Grpd]
  [x0 x1 : τ G]
  (p01 : τ (@= G x0 x1))
  [x2 : τ G]
  (p02 : τ (@= G x0 x2)) ⊢
  @path_nerve2_horn_zero_cancel G x0 x1 p01 x2 p02
  : τ (@=
      (@= G x0 x2)
      (@eq_trans G x0 x1 x2 p01
        (@eq_trans G x1 x0 x2 (@eq_sym G x0 x1 p01) p02))
      p02);

assert
  [G : Grpd]
  [x1 x2 : τ G]
  (p12 : τ (@= G x1 x2))
  [x0 : τ G]
  (p02 : τ (@= G x0 x2)) ⊢
  @path_nerve2_horn_two_cancel G x1 x2 p12 x0 p02
  : τ (@=
      (@= G x0 x2)
      (@eq_trans_right G x0 x1 x2
        (@eq_trans_right G x0 x2 x1 p02 (@eq_sym G x1 x2 p12))
        p12)
      p02);

// All three filler functions are sections of their algebraic restrictions.
assert (G : Grpd) ⊢
  @path_nerve2_fill_zero_section G
  : τ (@=
      (@Function_grpd
        (@PathNerve2HornZero G)
        (@PathNerve2HornZero G))
      (λ h : τ (@PathNerve2HornZero G),
        @path_nerve2_restrict_zero G (@path_nerve2_fill_zero G h))
      (λ h : τ (@PathNerve2HornZero G), h));

assert (G : Grpd) ⊢
  @path_nerve2_fill_one_section G
  : τ (@=
      (@Function_grpd
        (@PathNerve2HornOne G)
        (@PathNerve2HornOne G))
      (λ h : τ (@PathNerve2HornOne G),
        @path_nerve2_restrict_one G (@path_nerve2_fill_one G h))
      (λ h : τ (@PathNerve2HornOne G), h));

assert (G : Grpd) ⊢
  @path_nerve2_fill_two_section G
  : τ (@=
      (@Function_grpd
        (@PathNerve2HornTwo G)
        (@PathNerve2HornTwo G))
      (λ h : τ (@PathNerve2HornTwo G),
        @path_nerve2_restrict_two G (@path_nerve2_fill_two G h))
      (λ h : τ (@PathNerve2HornTwo G), h));

// Restriction and filling are whole path-category functors.
assert (G : Grpd) ⊢
  @path_nerve2_restrict_zero_func G
  : τ (Functor
      (Path_cat (@PathNerve2Simplex G))
      (Path_cat (@PathNerve2HornZero G)));

assert (G : Grpd) ⊢
  @path_nerve2_fill_zero_func G
  : τ (Functor
      (Path_cat (@PathNerve2HornZero G))
      (Path_cat (@PathNerve2Simplex G)));

// One next filler action remains at the generic Path-map owner.
assert [G : Grpd]
  (h k : τ (@PathNerve2HornZero G)) ⊢
  @fapp1_func
    (Path_cat (@PathNerve2HornZero G))
    (Path_cat (@PathNerve2Simplex G))
    (@path_nerve2_fill_zero_func G)
    h k
  : τ (Functor
      (Path_cat (@= (@PathNerve2HornZero G) h k))
      (Path_cat (@=
        (@PathNerve2Simplex G)
        (@path_nerve2_fill_zero G h)
        (@path_nerve2_fill_zero G k))));

// This bounded algebraic slice is not a claimed all-dimensional Kan object.
assertnot (G : Grpd) ⊢
  @PathNerve2Simplex G
  ≡ @Psh SemiDeltaPlus_cat;
