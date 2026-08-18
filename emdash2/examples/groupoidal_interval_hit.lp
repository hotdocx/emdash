/*
  Focused positive/negative reviewer for the groupoidal interval HIT.

  Dependent elimination computes judgmentally at both endpoints and on the
  generating dependent path.  Ordinary eq_ap remains the separate J-derived
  observation and is compared propositionally.
*/

require open emdash.emdash3_2_groupoidal_interval_hit;

assert ⊢ Interval_grpd : Grpd;

assert ⊢ interval_i0 : τ Interval_grpd;

assert ⊢ interval_i1 : τ Interval_grpd;

assert ⊢ interval_seg
  : τ (@= Interval_grpd interval_i0 interval_i1);

assert (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1)) ⊢
  @interval_ind D b0 b1 ell interval_i0
  ≡ b0;

assert (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1)) ⊢
  @interval_ind D b0 b1 ell interval_i1
  ≡ b1;

// The selected dependent path-constructor beta is literal computation.
assert (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1)) ⊢
  @eq_apd
    Interval_grpd D
    (λ x : τ Interval_grpd, @interval_ind D b0 b1 ell x)
    interval_i0 interval_i1 interval_seg
  ≡ ell;

assert (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1)) ⊢
  @interval_ind_beta_seg D b0 b1 ell
  ≡ @eq_refl
      (@PathOver
        Interval_grpd D
        interval_i0 interval_i1 interval_seg b0 b1)
      ell;

// The constant-family recursor inherits both point betas.
assert [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1)) ⊢
  @interval_rec B b0 b1 ell interval_i0
  ≡ b0;

assert [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1)) ⊢
  @interval_rec B b0 b1 ell interval_i1
  ≡ b1;

// Its dependent constructor beta is also judgmental.
assert [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1)) ⊢
  @eq_apd
    Interval_grpd
    (λ _ : τ Interval_grpd, B)
    (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
    interval_i0 interval_i1 interval_seg
  ≡ @const_pathover
      Interval_grpd B
      interval_i0 interval_i1 b0 b1 interval_seg ell;

// The ordinary path observation is the reviewed propositional bridge.
assert [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1)) ⊢
  @interval_rec_beta_seg_path B b0 b1 ell
  : τ (@=
      (@= B b0 b1)
      (@eq_ap
        Interval_grpd B
        (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
        interval_i0 interval_i1 interval_seg)
      ell);

// The interval signature does not collapse its endpoint constructors.
assertnot ⊢
  interval_i0
  ≡ interval_i1;

// An arbitrary dependent section does not acquire the HIT computation rule.
assertnot (D : τ Interval_grpd → Grpd)
  (f : Π x : τ Interval_grpd, τ (D x))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg
      (f interval_i0) (f interval_i1))) ⊢
  @eq_apd
    Interval_grpd D f
    interval_i0 interval_i1 interval_seg
  ≡ ell;

// Ordinary eq_ap remains propositional rather than a second runtime fold.
assertnot [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1)) ⊢
  @eq_ap
    Interval_grpd B
    (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
    interval_i0 interval_i1 interval_seg
  ≡ ell;
