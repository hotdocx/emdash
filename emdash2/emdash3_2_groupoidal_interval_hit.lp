/*
  Groupoidal interval HIT.

  The interval has two endpoints and one path between them.  Its dependent
  eliminator computes at both endpoints and judgmentally on the generating
  dependent path.  Ordinary recursion is the constant-family specialization;
  its eq_ap observation remains propositional through the reviewed generic
  PathOver-to-path bridge.

  This module is only the target-side HIT for the first free-inversion
  consumer.  It does not yet construct the WalkingArrow comparison functor,
  its whole mapping-object equivalence, or a generic Groupoidify reflector.
*/

require open emdash.emdash3_2_circle_hit;

// Formation and the two endpoint constructors.
constant symbol Interval_grpd : Grpd;

constant symbol interval_i0
  : τ Interval_grpd;

constant symbol interval_i1
  : τ Interval_grpd;

// The generating path freely identifies the two endpoints groupoidally.
constant symbol interval_seg
  : τ (@= Interval_grpd interval_i0 interval_i1);

/*
  Dependent elimination.  The constructor datum is a dependent path over
  interval_seg, so endpoint transport is retained rather than erased into a
  homogeneous equality.
*/
injective symbol interval_ind
  (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1))
  (x : τ Interval_grpd)
  : τ (D x);

// Point-constructor computation selects the two endpoint normal forms.
rule @interval_ind _ $b0 _ _ interval_i0
  ↪ $b0;

rule @interval_ind _ _ $b1 _ interval_i1
  ↪ $b1;

/*
  Dependent action on the generating path computes to the supplied PathOver
  constructor.  The measured owner-position audit requires D, b0, and b1:
  dropping D or either required endpoint guard fails subject reduction, while
  dropping b0 with D/b1 retained introduces an arity-mapping warning.
*/
// lhs-audit: keep 1,2,3 -- D/b1 preserve SR; b0 avoids an arity-map warning
rule @eq_apd
      Interval_grpd _
      (λ x : τ Interval_grpd,
        @interval_ind $D.[] $b0.[] $b1.[] $ell.[] x)
      _ _ interval_seg
  ↪ $ell;

// Typed views of the two runtime point betas.
symbol interval_ind_beta_i0
  (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1))
  : τ (@= (D interval_i0)
      (@interval_ind D b0 b1 ell interval_i0)
      b0)
≔ @eq_refl (D interval_i0) b0;

symbol interval_ind_beta_i1
  (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1))
  : τ (@= (D interval_i1)
      (@interval_ind D b0 b1 ell interval_i1)
      b1)
≔ @eq_refl (D interval_i1) b1;

// Typed view of the judgmental dependent path-constructor beta.
symbol interval_ind_beta_seg
  (D : τ Interval_grpd → Grpd)
  (b0 : τ (D interval_i0))
  (b1 : τ (D interval_i1))
  (ell : τ (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1))
  : τ (@=
      (@PathOver
        Interval_grpd D
        interval_i0 interval_i1 interval_seg b0 b1)
      (@eq_apd
        Interval_grpd D
        (λ x : τ Interval_grpd, @interval_ind D b0 b1 ell x)
        interval_i0 interval_i1 interval_seg)
      ell)
≔ @eq_refl
    (@PathOver
      Interval_grpd D
      interval_i0 interval_i1 interval_seg b0 b1)
    ell;

// Ordinary recursion is dependent induction over a constant family.
symbol interval_rec
  [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1))
  (x : τ Interval_grpd)
  : τ B
≔ @interval_ind
    (λ _ : τ Interval_grpd, B)
    b0
    b1
    (@const_pathover
      Interval_grpd B
      interval_i0 interval_i1 b0 b1 interval_seg ell)
    x;

// Point betas inherited judgmentally from interval_ind.
symbol interval_rec_beta_i0
  [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1))
  : τ (@= B (@interval_rec B b0 b1 ell interval_i0) b0)
≔ @eq_refl B b0;

symbol interval_rec_beta_i1
  [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1))
  : τ (@= B (@interval_rec B b0 b1 ell interval_i1) b1)
≔ @eq_refl B b1;

// Constant-family dependent path beta inherited from interval_ind.
symbol interval_rec_beta_seg
  [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1))
  : τ (@=
      (@PathOver
        Interval_grpd
        (λ _ : τ Interval_grpd, B)
        interval_i0 interval_i1 interval_seg b0 b1)
      (@eq_apd
        Interval_grpd
        (λ _ : τ Interval_grpd, B)
        (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
        interval_i0 interval_i1 interval_seg)
      (@const_pathover
        Interval_grpd B
        interval_i0 interval_i1 b0 b1 interval_seg ell))
≔ @interval_ind_beta_seg
    (λ _ : τ Interval_grpd, B)
    b0
    b1
    (@const_pathover
      Interval_grpd B
      interval_i0 interval_i1 b0 b1 interval_seg ell);

/*
  Ordinary ap computation is a proposition, not a competing runtime fold.
  The two generic observations are reused from the Circle module; no new
  global eq_ap owner is introduced here.
*/
symbol interval_rec_beta_seg_path
  [B : Grpd]
  (b0 b1 : τ B)
  (ell : τ (@= B b0 b1))
  : τ (@=
      (@= B b0 b1)
      (@eq_ap
        Interval_grpd B
        (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
        interval_i0 interval_i1 interval_seg)
      ell)
≔ @eq_trans
    (@= B b0 b1)
    (@eq_ap
      Interval_grpd B
      (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
      interval_i0 interval_i1 interval_seg)
    (@const_pathover_path
      Interval_grpd B
      interval_i0 interval_i1 b0 b1 interval_seg
      (@eq_apd
        Interval_grpd
        (λ _ : τ Interval_grpd, B)
        (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
        interval_i0 interval_i1 interval_seg))
    ell
    (@eq_sym
      (@= B b0 b1)
      (@const_pathover_path
        Interval_grpd B
        interval_i0 interval_i1 b0 b1 interval_seg
        (@eq_apd
          Interval_grpd
          (λ _ : τ Interval_grpd, B)
          (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
          interval_i0 interval_i1 interval_seg))
      (@eq_ap
        Interval_grpd B
        (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
        interval_i0 interval_i1 interval_seg)
      (@const_pathover_path_eq_apd
        Interval_grpd B
        (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
        interval_i0 interval_i1 interval_seg))
    (@eq_trans
      (@= B b0 b1)
      (@const_pathover_path
        Interval_grpd B
        interval_i0 interval_i1 b0 b1 interval_seg
        (@eq_apd
          Interval_grpd
          (λ _ : τ Interval_grpd, B)
          (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
          interval_i0 interval_i1 interval_seg))
      (@const_pathover_path
        Interval_grpd B
        interval_i0 interval_i1 b0 b1 interval_seg
        (@const_pathover
          Interval_grpd B
          interval_i0 interval_i1 b0 b1 interval_seg ell))
      ell
      (@eq_ap
        (@PathOver
          Interval_grpd
          (λ _ : τ Interval_grpd, B)
          interval_i0 interval_i1 interval_seg b0 b1)
        (@= B b0 b1)
        (λ q : τ (@PathOver
            Interval_grpd
            (λ _ : τ Interval_grpd, B)
            interval_i0 interval_i1 interval_seg b0 b1),
          @const_pathover_path
            Interval_grpd B
            interval_i0 interval_i1 b0 b1 interval_seg q)
        (@eq_apd
          Interval_grpd
          (λ _ : τ Interval_grpd, B)
          (λ x : τ Interval_grpd, @interval_rec B b0 b1 ell x)
          interval_i0 interval_i1 interval_seg)
        (@const_pathover
          Interval_grpd B
          interval_i0 interval_i1 b0 b1 interval_seg ell)
        (@interval_rec_beta_seg B b0 b1 ell))
      (@const_pathover_path_const
        Interval_grpd B
        interval_i0 interval_i1 interval_seg b0 b1 ell));
