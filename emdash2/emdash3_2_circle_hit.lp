/*
  One-dimensional groupoidal Circle HIT signature.

  Formation, base, loop, dimension evidence, and dependent elimination are
  opaque signature data. The point-constructor beta is the sole runtime rule;
  loop computation is propositional, following the active HIT policy and the
  HoTT Book presentation. The inverse loop is derived from equality symmetry.

  This first tranche does not yet construct the integer code family or prove
  the loop-space equivalence.
*/

require open emdash.emdash3_2;
require open emdash.emdash3_2_integer_localization;

// Circle formation and generating point/path constructors.
constant symbol Circle_grpd : Grpd;

constant symbol circle_base
  : τ Circle_grpd;

constant symbol circle_loop
  : τ (@= Circle_grpd circle_base circle_base);

// Selected one-dimensional HIT evidence; every Circle path type is a set.
constant symbol circle_is_groupoid
  : τ (IsGroupoidGrpd Circle_grpd);

// The based loop space is set-valued by the dimensional signature.
symbol circle_loop_space_is_set
  : τ (IsSetGrpd (@= Circle_grpd circle_base circle_base))
≔ circle_is_groupoid circle_base circle_base;

// The inverse generator is intrinsic equality symmetry, not new HIT data.
symbol circle_loop_inverse
  : τ (@= Circle_grpd circle_base circle_base)
≔ @eq_sym Circle_grpd circle_base circle_base circle_loop;

/*
  Dependent Circle elimination. The loop datum is one dependent path over the
  generating loop. No truncation premise is imposed on the motive: the
  one-dimensional evidence is separate signature data, as for WalkingEnd.
*/
injective symbol circle_ind
  (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b))
  (x : τ Circle_grpd)
  : τ (D x);

// Point-constructor computation is the selected runtime normal form.
rule @circle_ind _ $b _ circle_base ↪ $b;

/*
  Dependent action on the generating path computes to the supplied PathOver
  constructor. Circle, circle_ind, and circle_loop select this normal form;
  the outer family and endpoints remain inferred. The nested motive and base
  are retained because replacing either by `_` fails subject reduction.
*/
// lhs-audit: keep 1,2 -- nested circle_ind motive/base are subject-reduction guards
rule @eq_apd
      Circle_grpd _
      (λ x : τ Circle_grpd,
        @circle_ind $D.[] $b.[] $ell.[] x)
      _ _ circle_loop
  ↪ $ell;

// Typed view of the runtime point beta.
symbol circle_ind_beta_base
  (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b))
  : τ (@= (D circle_base)
      (@circle_ind D b ell circle_base)
      b)
≔ @eq_refl (D circle_base) b;

// Typed view of the runtime path-constructor beta.
symbol circle_ind_beta_loop
  (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b))
  : τ (@=
      (@PathOver
        Circle_grpd D
        circle_base circle_base circle_loop b b)
      (@eq_apd
        Circle_grpd D
        (λ x : τ Circle_grpd, @circle_ind D b ell x)
        circle_base circle_base circle_loop)
      ell)
≔ @eq_refl
    (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b)
    ell;

// Ordinary recursion is dependent induction over a constant family.
symbol circle_rec
  [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b))
  (x : τ Circle_grpd)
  : τ B
≔ @circle_ind
    (λ _ : τ Circle_grpd, B)
    b
    (@const_pathover
      Circle_grpd B
      circle_base circle_base b b circle_loop ell)
    x;

// Ordinary-recursion point beta, inherited from circle_ind.
symbol circle_rec_beta_base
  [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b))
  : τ (@= B (@circle_rec B b ell circle_base) b)
≔ @eq_refl B b;

// Dependent loop beta inherited judgmentally from circle_ind.
symbol circle_rec_beta_loop
  [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b))
  : τ (@=
      (@PathOver
        Circle_grpd
        (λ _ : τ Circle_grpd, B)
        circle_base circle_base circle_loop b b)
      (@eq_apd
        Circle_grpd
        (λ _ : τ Circle_grpd, B)
        (λ x : τ Circle_grpd, @circle_rec B b ell x)
        circle_base circle_base circle_loop)
      (@const_pathover
        Circle_grpd B
        circle_base circle_base b b circle_loop ell))
≔ @circle_ind_beta_loop
    (λ _ : τ Circle_grpd, B)
    b
    (@const_pathover
      Circle_grpd B
      circle_base circle_base b b circle_loop ell);

/*
  Two generic constant-family observations turn the dependent loop beta into
  the ordinary `ap` equation expected from Circle recursion. They are proved
  by the existing right-based path induction and add no computation rule.
*/
symbol const_pathover_path_eq_apd
  [A B : Grpd]
  (f : τ A → τ B)
  [x y : τ A]
  (p : τ (@= A x y))
  : τ (@=
      (@= B (f x) (f y))
      (@const_pathover_path
        A B x y (f x) (f y) p
        (@eq_apd
          A (λ _ : τ A, B) f x y p))
      (@eq_ap A B f x y p))
≔ @ind_eqr
    A
    y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @=
          (@= B (f x) (f y))
          (@const_pathover_path
            A B x y (f x) (f y) p
            (@eq_apd
              A (λ _ : τ A, B) f x y p))
          (@eq_ap A B f x y p))
    (@eq_refl (@= B (f y) (f y)) (@eq_refl B (f y)))
    x
    p;

symbol const_pathover_path_const
  [A B : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  [u v : τ B]
  (q : τ (@= B u v))
  : τ (@=
      (@= B u v)
      (@const_pathover_path
        A B x y u v p
        (@const_pathover A B x y u v p q))
      q)
≔ @ind_eqr
    A
    y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @Pi_grpd B
          (λ u : τ B,
            @Pi_grpd B
              (λ v : τ B,
                @Pi_grpd
                  (@= B u v)
                  (λ q : τ (@= B u v),
                    @=
                      (@= B u v)
                      (@const_pathover_path
                        A B x y u v p
                        (@const_pathover A B x y u v p q))
                      q))))
    (λ u : τ B,
      λ v : τ B,
        λ q : τ (@= B u v),
          @eq_refl (@= B u v) q)
    x
    p
    u
    v
    q;

// Ordinary `ap` loop beta extracted propositionally from the HIT PathOver beta.
symbol circle_rec_beta_loop_path
  [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b))
  : τ (@=
      (@= B b b)
      (@eq_ap
        Circle_grpd B
        (λ x : τ Circle_grpd, @circle_rec B b ell x)
        circle_base circle_base circle_loop)
      ell)
≔ @eq_trans
    (@= B b b)
    (@eq_ap
      Circle_grpd B
      (λ x : τ Circle_grpd, @circle_rec B b ell x)
      circle_base circle_base circle_loop)
    (@const_pathover_path
      Circle_grpd B
      circle_base circle_base b b circle_loop
      (@eq_apd
        Circle_grpd
        (λ _ : τ Circle_grpd, B)
        (λ x : τ Circle_grpd, @circle_rec B b ell x)
        circle_base circle_base circle_loop))
    ell
    (@eq_sym
      (@= B b b)
      (@const_pathover_path
        Circle_grpd B
        circle_base circle_base b b circle_loop
        (@eq_apd
          Circle_grpd
          (λ _ : τ Circle_grpd, B)
          (λ x : τ Circle_grpd, @circle_rec B b ell x)
          circle_base circle_base circle_loop))
      (@eq_ap
        Circle_grpd B
        (λ x : τ Circle_grpd, @circle_rec B b ell x)
        circle_base circle_base circle_loop)
      (@const_pathover_path_eq_apd
        Circle_grpd B
        (λ x : τ Circle_grpd, @circle_rec B b ell x)
        circle_base circle_base circle_loop))
    (@eq_trans
      (@= B b b)
      (@const_pathover_path
        Circle_grpd B
        circle_base circle_base b b circle_loop
        (@eq_apd
          Circle_grpd
          (λ _ : τ Circle_grpd, B)
          (λ x : τ Circle_grpd, @circle_rec B b ell x)
          circle_base circle_base circle_loop))
      (@const_pathover_path
        Circle_grpd B
        circle_base circle_base b b circle_loop
        (@const_pathover
          Circle_grpd B
          circle_base circle_base b b circle_loop ell))
      ell
      (@eq_ap
        (@PathOver
          Circle_grpd
          (λ _ : τ Circle_grpd, B)
          circle_base circle_base circle_loop b b)
        (@= B b b)
        (λ q : τ (@PathOver
            Circle_grpd
            (λ _ : τ Circle_grpd, B)
            circle_base circle_base circle_loop b b),
          @const_pathover_path
            Circle_grpd B
            circle_base circle_base b b circle_loop q)
        (@eq_apd
          Circle_grpd
          (λ _ : τ Circle_grpd, B)
          (λ x : τ Circle_grpd, @circle_rec B b ell x)
          circle_base circle_base circle_loop)
        (@const_pathover
          Circle_grpd B
          circle_base circle_base b b circle_loop ell)
        (@circle_rec_beta_loop B b ell))
      (@const_pathover_path_const
        Circle_grpd B
        circle_base circle_base circle_loop b b ell));

// Universal-cover code family with successor monodromy.
symbol CircleCode
  (x : τ Circle_grpd)
  : Grpd
≔ @circle_rec
    Grpd_grpd
    Integer_grpd
    integer_succ_path
    x;

symbol circle_Code_beta_base
  : τ (@= Grpd_grpd (CircleCode circle_base) Integer_grpd)
≔ @eq_refl Grpd_grpd Integer_grpd;

symbol circle_Code_beta_loop
  : τ (@=
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      integer_succ_path)
≔ @circle_rec_beta_loop_path
    Grpd_grpd Integer_grpd integer_succ_path;

// Encode a path from the base by transporting zero in the code family.
symbol circle_encode
  [x : τ Circle_grpd]
  (p : τ (@= Circle_grpd circle_base x))
  : τ (CircleCode x)
≔ @coe_grpd
    (CircleCode circle_base)
    (CircleCode x)
    (@eq_ap
      Circle_grpd Grpd_grpd
      CircleCode
      circle_base x p)
    integer_zero;

symbol circle_encode_refl
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (@eq_refl Circle_grpd circle_base))
      integer_zero)
≔ @eq_refl Integer_grpd integer_zero;

// The generator encodes as successor of zero, propositionally and rule-free.
symbol circle_encode_loop
  : τ (@= Integer_grpd
      (@circle_encode circle_base circle_loop)
      (integer_succ integer_zero))
≔ @eq_trans
    Integer_grpd
    (@circle_encode circle_base circle_loop)
    (@coe_grpd
      Integer_grpd Integer_grpd integer_succ_path integer_zero)
    (integer_succ integer_zero)
    (@eq_ap
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      Integer_grpd
      (λ q : τ (@= Grpd_grpd Integer_grpd Integer_grpd),
        @coe_grpd Integer_grpd Integer_grpd q integer_zero)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      integer_succ_path
      circle_Code_beta_loop)
    (integer_succ_path_coe integer_zero);

/*
  Integer-indexed loop powers.

  The stage representative is defined by simultaneous cancellation rather
  than by a signed normal-form datatype. At (succ n,succ x) it reduces to the
  preceding (n,x) stage, so the telescope coherence is literal reflexivity.
*/
symbol circle_nat_power
  (n : τ Nat_grpd)
  : τ (@= Circle_grpd circle_base circle_base)
≔ @nat_elim
    (λ _ : τ Nat_grpd,
      @= Circle_grpd circle_base circle_base)
    (@eq_refl Circle_grpd circle_base)
    (λ _ : τ Nat_grpd,
      λ p : τ (@= Circle_grpd circle_base circle_base),
        @eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p circle_loop)
    n;

symbol circle_nat_inverse_power
  (n : τ Nat_grpd)
  : τ (@= Circle_grpd circle_base circle_base)
≔ @nat_elim
    (λ _ : τ Nat_grpd,
      @= Circle_grpd circle_base circle_base)
    (@eq_refl Circle_grpd circle_base)
    (λ _ : τ Nat_grpd,
      λ p : τ (@= Circle_grpd circle_base circle_base),
        @eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p circle_loop_inverse)
    n;

symbol circle_integer_stage_power
  (n x : τ Nat_grpd)
  : τ (@= Circle_grpd circle_base circle_base)
≔ (@nat_elim
      (λ _ : τ Nat_grpd,
        @Function_grpd
          Nat_grpd
          (@= Circle_grpd circle_base circle_base))
      (λ x : τ Nat_grpd, circle_nat_power x)
      (λ n : τ Nat_grpd,
        λ previous : τ (@Function_grpd
            Nat_grpd
            (@= Circle_grpd circle_base circle_base)),
          λ x : τ Nat_grpd,
            @nat_elim
              (λ _ : τ Nat_grpd,
                @= Circle_grpd circle_base circle_base)
              (circle_nat_inverse_power (succ n))
              (λ x0 : τ Nat_grpd,
                λ _ : τ (@= Circle_grpd circle_base circle_base),
                  previous x0)
              x)
      n)
    x;

// The localization relation is respected by definitional diagonal reduction.
symbol circle_integer_stage_power_step
  (n x : τ Nat_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_integer_stage_power (succ n) (succ x))
      (circle_integer_stage_power n x))
≔ @eq_refl
    (@= Circle_grpd circle_base circle_base)
    (circle_integer_stage_power n x);

// Based decoder from the trusted integer localization to Circle loops.
symbol circle_decode
  (z : τ Integer_grpd)
  : τ (@= Circle_grpd circle_base circle_base)
≔ @integer_elim
    (@= Circle_grpd circle_base circle_base)
    circle_loop_space_is_set
    circle_integer_stage_power
    circle_integer_stage_power_step
    z;

symbol circle_decode_zero
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_decode integer_zero)
      (@eq_refl Circle_grpd circle_base))
≔ @eq_refl
    (@= Circle_grpd circle_base circle_base)
    (@eq_refl Circle_grpd circle_base);

symbol circle_decode_of_nat
  (n : τ Nat_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_decode (integer_of_nat n))
      (circle_nat_power n))
≔ @eq_refl
    (@= Circle_grpd circle_base circle_base)
    (circle_nat_power n);

symbol circle_decode_neg_one
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_decode integer_neg_one)
      circle_loop_inverse)
≔ @eq_refl
    (@= Circle_grpd circle_base circle_base)
    circle_loop_inverse;

// Right cancellation against a path inverse, derived from generic J.
symbol eq_trans_right_sym_cancel
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  [w : τ A]
  (r : τ (@= A w x))
  : τ (@=
      (@= A w x)
      (@eq_trans
        A w y x
        (@eq_trans A w x y r p)
        (@eq_sym A x y p))
      r)
≔ @ind_eqr
    A
    y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @Pi_grpd A
          (λ w : τ A,
            @Pi_grpd
              (@= A w x)
              (λ r : τ (@= A w x),
                @=
                  (@= A w x)
                  (@eq_trans
                    A w y x
                    (@eq_trans A w x y r p)
                    (@eq_sym A x y p))
                  r)))
    (λ w : τ A,
      λ r : τ (@= A w y),
        @eq_trans
          (@= A w y)
          (@eq_trans
            A w y y
            (@eq_trans A w y y r (@eq_refl A y))
            (@eq_refl A y))
          (@eq_trans A w y y r (@eq_refl A y))
          r
          (@eq_ap
            (@= A w y)
            (@= A w y)
            (λ s : τ (@= A w y),
              @eq_trans A w y y s (@eq_refl A y))
            (@eq_trans A w y y r (@eq_refl A y))
            r
            (@eq_trans_right_unit A w y r))
          (@eq_trans_right_unit A w y r))
    x
    p
    w
    r;

// The other right-adjacent cancellation order, also derived from generic J.
symbol eq_trans_sym_right_cancel
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  [w : τ A]
  (r : τ (@= A w y))
  : τ (@=
      (@= A w y)
      (@eq_trans
        A w x y
        (@eq_trans
          A w y x
          r
          (@eq_sym A x y p))
        p)
      r)
≔ @ind_eqr
    A
    y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @Pi_grpd A
          (λ w : τ A,
            @Pi_grpd
              (@= A w y)
              (λ r : τ (@= A w y),
                @=
                  (@= A w y)
                  (@eq_trans
                    A w x y
                    (@eq_trans
                      A w y x
                      r
                      (@eq_sym A x y p))
                    p)
                  r)))
    (λ w : τ A,
      λ r : τ (@= A w y),
        @eq_trans
          (@= A w y)
          (@eq_trans
            A w y y
            (@eq_trans A w y y r (@eq_refl A y))
            (@eq_refl A y))
          (@eq_trans A w y y r (@eq_refl A y))
          r
          (@eq_ap
            (@= A w y)
            (@= A w y)
            (λ s : τ (@= A w y),
              @eq_trans A w y y s (@eq_refl A y))
            (@eq_trans A w y y r (@eq_refl A y))
            r
            (@eq_trans_right_unit A w y r))
          (@eq_trans_right_unit A w y r))
    x
    p
    w
    r;

/*
  The inverse-prefix boundary followed by the generator cancels. The chosen
  power recursion makes the cancellation literally adjacent.
*/
symbol circle_nat_inverse_power_succ_cancel
  (n : τ Nat_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        (circle_nat_inverse_power (succ n))
        circle_loop)
      (circle_nat_inverse_power n))
≔ @eq_trans_sym_right_cancel
    Circle_grpd
    circle_base circle_base
    circle_loop
    circle_base
    (circle_nat_inverse_power n);

symbol circle_integer_stage_power_zero
  (n : τ Nat_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_integer_stage_power n zero)
      (circle_nat_inverse_power n))
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @=
        (@= Circle_grpd circle_base circle_base)
        (circle_integer_stage_power n zero)
        (circle_nat_inverse_power n))
    (@eq_refl
      (@= Circle_grpd circle_base circle_base)
      (@eq_refl Circle_grpd circle_base))
    (λ n : τ Nat_grpd,
      λ _ : τ (@=
        (@= Circle_grpd circle_base circle_base)
        (circle_integer_stage_power n zero)
        (circle_nat_inverse_power n)),
      @eq_refl
        (@= Circle_grpd circle_base circle_base)
        (circle_nat_inverse_power (succ n)))
    n;

// Successor of a stage appends one generating loop to its decoded power.
symbol circle_integer_stage_power_succ
  (n x : τ Nat_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_integer_stage_power n (succ x))
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        (circle_integer_stage_power n x)
        circle_loop))
≔ (@nat_elim
      (λ n : τ Nat_grpd,
        @Pi_grpd Nat_grpd
          (λ x : τ Nat_grpd,
            @=
              (@= Circle_grpd circle_base circle_base)
              (circle_integer_stage_power n (succ x))
              (@eq_trans
                Circle_grpd
                circle_base circle_base circle_base
                (circle_integer_stage_power n x)
                circle_loop)))
      (λ x : τ Nat_grpd,
        @eq_refl
          (@= Circle_grpd circle_base circle_base)
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (circle_nat_power x)
            circle_loop))
      (λ n : τ Nat_grpd,
        λ previous : τ (@Pi_grpd Nat_grpd
            (λ x : τ Nat_grpd,
              @=
                (@= Circle_grpd circle_base circle_base)
                (circle_integer_stage_power n (succ x))
                (@eq_trans
                  Circle_grpd
                  circle_base circle_base circle_base
                  (circle_integer_stage_power n x)
                  circle_loop))),
          λ x : τ Nat_grpd,
            @nat_elim
              (λ x : τ Nat_grpd,
                @=
                  (@= Circle_grpd circle_base circle_base)
                  (circle_integer_stage_power (succ n) (succ x))
                  (@eq_trans
                    Circle_grpd
                    circle_base circle_base circle_base
                    (circle_integer_stage_power (succ n) x)
                    circle_loop))
              (@eq_trans
                (@= Circle_grpd circle_base circle_base)
                (circle_integer_stage_power n zero)
                (circle_nat_inverse_power n)
                (@eq_trans
                  Circle_grpd
                  circle_base circle_base circle_base
                  (circle_nat_inverse_power (succ n))
                  circle_loop)
                (@circle_integer_stage_power_zero n)
                (@eq_sym
                  (@= Circle_grpd circle_base circle_base)
                  (@eq_trans
                    Circle_grpd
                    circle_base circle_base circle_base
                    (circle_nat_inverse_power (succ n))
                    circle_loop)
                  (circle_nat_inverse_power n)
                  (@circle_nat_inverse_power_succ_cancel n)))
              (λ x0 : τ Nat_grpd,
                λ _ : τ (@=
                  (@= Circle_grpd circle_base circle_base)
                  (circle_integer_stage_power (succ n) (succ x0))
                  (@eq_trans
                    Circle_grpd
                    circle_base circle_base circle_base
                    (circle_integer_stage_power (succ n) x0)
                    circle_loop)),
                  previous x0)
              x)
      n)
    x;

// Motive asserting that Integer successor appends the Circle generator.
symbol CircleDecodeSuccMotive
  (z : τ Integer_grpd)
  : Grpd
≔ @=
    (@= Circle_grpd circle_base circle_base)
    (circle_decode (integer_succ z))
    (@eq_trans
      Circle_grpd
      circle_base circle_base circle_base
      (circle_decode z)
      circle_loop);

symbol circle_decode_succ_motive_is_prop
  (z : τ Integer_grpd)
  : τ (IsPropGrpd (CircleDecodeSuccMotive z))
≔ circle_loop_space_is_set
    (circle_decode (integer_succ z))
    (@eq_trans
      Circle_grpd
      circle_base circle_base circle_base
      (circle_decode z)
      circle_loop);

symbol circle_decode_succ_motive_is_set
  (z : τ Integer_grpd)
  : τ (IsSetGrpd (CircleDecodeSuccMotive z))
≔ @is_trunc_grpd_succ
    trunc_minus_one
    (CircleDecodeSuccMotive z)
    (circle_decode_succ_motive_is_prop z);

symbol circle_decode_succ_stage
  (n x : τ Nat_grpd)
  : τ (CircleDecodeSuccMotive (integer_stage n x))
≔ @circle_integer_stage_power_succ n x;

symbol circle_decode_succ_stage_coherence
  (n x : τ Nat_grpd)
  : τ (@PathOver
      Integer_grpd
      CircleDecodeSuccMotive
      (integer_stage (succ n) (succ x))
      (integer_stage n x)
      (integer_stage_step n x)
      (circle_decode_succ_stage (succ n) (succ x))
      (circle_decode_succ_stage n x))
≔ @prop_family_pathover
    Integer_grpd
    CircleDecodeSuccMotive
    circle_decode_succ_motive_is_prop
    (integer_stage (succ n) (succ x))
    (integer_stage n x)
    (integer_stage_step n x)
    (circle_decode_succ_stage (succ n) (succ x))
    (circle_decode_succ_stage n x);

symbol circle_decode_succ
  (z : τ Integer_grpd)
  : τ (CircleDecodeSuccMotive z)
≔ @integer_ind
    CircleDecodeSuccMotive
    circle_decode_succ_motive_is_set
    circle_decode_succ_stage
    circle_decode_succ_stage_coherence
    z;

// The Code transport around the generator is the Integer successor.
symbol circle_Code_transport_loop
  (z : τ Integer_grpd)
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop)
        z)
      (integer_succ z))
≔ @eq_trans
    Integer_grpd
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      z)
    (@coe_grpd Integer_grpd Integer_grpd integer_succ_path z)
    (integer_succ z)
    (@eq_ap
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      Integer_grpd
      (λ q : τ (@= Grpd_grpd Integer_grpd Integer_grpd),
        @coe_grpd Integer_grpd Integer_grpd q z)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      integer_succ_path
      circle_Code_beta_loop)
    (integer_succ_path_coe z);

/*
  Backward transport in a varying function family. The domain is first moved
  forward by universe transport, while the result is moved backward in the
  codomain family. Generic J proves the comparison without a transport rule.
*/
symbol function_family_transport
  [A : Grpd]
  (B C : τ A → Grpd)
  [x y : τ A]
  (p : τ (@= A x y))
  (h : τ (@Function_grpd (B y) (C y)))
  : τ (@=
      (@Function_grpd (B x) (C x))
      (@ind_eq
        A x y p
        (λ t : τ A, @Function_grpd (B t) (C t))
        h)
      (λ b : τ (B x),
        @ind_eq
          A x y p
          C
          (h (@coe_grpd
            (B x)
            (B y)
            (@eq_ap A Grpd_grpd B x y p)
            b))))
≔ @ind_eqr
    A
    y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @Pi_grpd
          (@Function_grpd (B y) (C y))
          (λ h : τ (@Function_grpd (B y) (C y)),
            @=
              (@Function_grpd (B x) (C x))
              (@ind_eq
                A x y p
                (λ t : τ A, @Function_grpd (B t) (C t))
                h)
              (λ b : τ (B x),
                @ind_eq
                  A x y p
                  C
                  (h (@coe_grpd
                    (B x)
                    (B y)
                    (@eq_ap A Grpd_grpd B x y p)
                    b)))))
    (λ h : τ (@Function_grpd (B y) (C y)),
      @eq_refl (@Function_grpd (B y) (C y)) h)
    x
    p
    h;

// Backward transport of a based path appends the inverse base path.
symbol based_path_family_transport
  [A : Grpd]
  [a x y : τ A]
  (p : τ (@= A x y))
  (q : τ (@= A a y))
  : τ (@=
      (@= A a x)
      (@ind_eq
        A x y p
        (λ t : τ A, @= A a t)
        q)
      (@eq_trans
        A a y x
        q
        (@eq_sym A x y p)))
≔ @ind_eqr
    A
    y
    (λ x : τ A,
      λ p : τ (@= A x y),
        @Pi_grpd
          (@= A a y)
          (λ q : τ (@= A a y),
            @=
              (@= A a x)
              (@ind_eq
                A x y p
                (λ t : τ A, @= A a t)
                q)
              (@eq_trans
                A a y x
                q
                (@eq_sym A x y p))))
    (λ q : τ (@= A a y),
      @eq_sym
        (@= A a y)
        (@eq_trans A a y y q (@eq_refl A y))
        q
        (@eq_trans_right_unit A a y q))
    x
    p
    q;

symbol CircleDecodeMotive
  (x : τ Circle_grpd)
  : Grpd
≔ @Function_grpd
    (CircleCode x)
    (@= Circle_grpd circle_base x);

symbol circle_decode_function_transport
  : τ (@=
      (CircleDecodeMotive circle_base)
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        CircleDecodeMotive
        circle_decode)
      (λ z : τ Integer_grpd,
        @ind_eq
          Circle_grpd
          circle_base circle_base circle_loop
          (λ x : τ Circle_grpd,
            @= Circle_grpd circle_base x)
          (circle_decode
            (@coe_grpd
              Integer_grpd
              Integer_grpd
              (@eq_ap
                Circle_grpd Grpd_grpd
                CircleCode
                circle_base circle_base circle_loop)
              z))))
≔ @function_family_transport
    Circle_grpd
    CircleCode
    (λ x : τ Circle_grpd,
      @= Circle_grpd circle_base x)
    circle_base circle_base circle_loop
    circle_decode;

symbol circle_based_path_transport_loop
  (q : τ (@= Circle_grpd circle_base circle_base))
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        q)
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        q circle_loop_inverse))
≔ @based_path_family_transport
    Circle_grpd
    circle_base
    circle_base circle_base
    circle_loop
    q;

// Pointwise formula for transporting the based decoder backward around loop.
symbol circle_decode_transport_formula
  (z : τ Integer_grpd)
  : τ (@= Circle_grpd circle_base circle_base)
≔ @ind_eq
    Circle_grpd
    circle_base circle_base circle_loop
    (λ x : τ Circle_grpd,
      @= Circle_grpd circle_base x)
    (circle_decode
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop)
        z));

symbol circle_decode_transport_Code_step
  (z : τ Integer_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_decode_transport_formula z)
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        (circle_decode (integer_succ z))))
≔ @eq_ap
    (@= Circle_grpd circle_base circle_base)
    (@= Circle_grpd circle_base circle_base)
    (λ q : τ (@= Circle_grpd circle_base circle_base),
      @ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        q)
    (circle_decode
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop)
        z))
    (circle_decode (integer_succ z))
    (@eq_ap
      Integer_grpd
      (@= Circle_grpd circle_base circle_base)
      circle_decode
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop)
        z)
      (integer_succ z)
      (@circle_Code_transport_loop z));

symbol circle_decode_transport_succ_step
  (z : τ Integer_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        (circle_decode (integer_succ z)))
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          (circle_decode z)
          circle_loop)))
≔ @eq_ap
    (@= Circle_grpd circle_base circle_base)
    (@= Circle_grpd circle_base circle_base)
    (λ q : τ (@= Circle_grpd circle_base circle_base),
      @ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        q)
    (circle_decode (integer_succ z))
    (@eq_trans
      Circle_grpd
      circle_base circle_base circle_base
      (circle_decode z)
      circle_loop)
    (@circle_decode_succ z);

symbol circle_decode_transport_formula_to_base
  (z : τ Integer_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_decode_transport_formula z)
      (circle_decode z))
≔ @eq_trans
    (@= Circle_grpd circle_base circle_base)
    (circle_decode_transport_formula z)
    (@ind_eq
      Circle_grpd
      circle_base circle_base circle_loop
      (λ x : τ Circle_grpd,
        @= Circle_grpd circle_base x)
      (circle_decode (integer_succ z)))
    (circle_decode z)
    (@circle_decode_transport_Code_step z)
    (@eq_trans
      (@= Circle_grpd circle_base circle_base)
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        (circle_decode (integer_succ z)))
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        (λ x : τ Circle_grpd,
          @= Circle_grpd circle_base x)
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          (circle_decode z)
          circle_loop))
      (circle_decode z)
      (@circle_decode_transport_succ_step z)
      (@eq_trans
        (@= Circle_grpd circle_base circle_base)
        (@ind_eq
          Circle_grpd
          circle_base circle_base circle_loop
          (λ x : τ Circle_grpd,
            @= Circle_grpd circle_base x)
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (circle_decode z)
            circle_loop))
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (circle_decode z)
            circle_loop)
          circle_loop_inverse)
        (circle_decode z)
        (@circle_based_path_transport_loop
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (circle_decode z)
            circle_loop))
        (@eq_trans_right_sym_cancel
          Circle_grpd
          circle_base circle_base
          circle_loop
          circle_base
          (circle_decode z))));

symbol circle_decode_loop_pointwise
  : τ (@PiPointwisePath
      Integer_grpd
      (λ _ : τ Integer_grpd,
        @= Circle_grpd circle_base circle_base)
      circle_decode
      circle_decode_transport_formula)
≔ λ z : τ Integer_grpd,
    @eq_sym
      (@= Circle_grpd circle_base circle_base)
      (circle_decode_transport_formula z)
      (circle_decode z)
      (@circle_decode_transport_formula_to_base z);

symbol circle_decode_loop_function_path
  : τ (@=
      (CircleDecodeMotive circle_base)
      circle_decode
      circle_decode_transport_formula)
≔ @PiFunext
    Integer_grpd
    (λ _ : τ Integer_grpd,
      @= Circle_grpd circle_base circle_base)
    circle_decode
    circle_decode_transport_formula
    circle_decode_loop_pointwise;

// The based decoder is invariant under the Circle generating loop.
symbol circle_decode_loop_coherence
  : τ (@PathOver
      Circle_grpd
      CircleDecodeMotive
      circle_base circle_base circle_loop
      circle_decode circle_decode)
≔ @eq_trans
    (CircleDecodeMotive circle_base)
    circle_decode
    circle_decode_transport_formula
    (@ind_eq
      Circle_grpd
      circle_base circle_base circle_loop
      CircleDecodeMotive
      circle_decode)
    circle_decode_loop_function_path
    (@eq_sym
      (CircleDecodeMotive circle_base)
      (@ind_eq
        Circle_grpd
        circle_base circle_base circle_loop
        CircleDecodeMotive
        circle_decode)
      circle_decode_transport_formula
      circle_decode_function_transport);

// Endpoint-dependent decoder obtained from the checked loop coherence.
symbol circle_decode_function
  (x : τ Circle_grpd)
  : τ (CircleDecodeMotive x)
≔ @circle_ind
    CircleDecodeMotive
    circle_decode
    circle_decode_loop_coherence
    x;

symbol circle_decode_at
  [x : τ Circle_grpd]
  (z : τ (CircleCode x))
  : τ (@= Circle_grpd circle_base x)
≔ circle_decode_function x z;

symbol circle_decode_at_beta_base
  (z : τ Integer_grpd)
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (@circle_decode_at circle_base z)
      (circle_decode z))
≔ @eq_refl
    (@= Circle_grpd circle_base circle_base)
    (circle_decode z);

symbol circle_decode_function_beta_loop
  : τ (@=
      (@PathOver
        Circle_grpd
        CircleDecodeMotive
        circle_base circle_base circle_loop
        circle_decode circle_decode)
      (@eq_apd
        Circle_grpd
        CircleDecodeMotive
        circle_decode_function
        circle_base circle_base circle_loop)
      circle_decode_loop_coherence)
≔ @circle_ind_beta_loop
    CircleDecodeMotive
    circle_decode
    circle_decode_loop_coherence;

// Decoding after encoding is identity, by ordinary endpoint path induction.
symbol circle_decode_encode
  [x : τ Circle_grpd]
  (p : τ (@= Circle_grpd circle_base x))
  : τ (@=
      (@= Circle_grpd circle_base x)
      (@circle_decode_at x (@circle_encode x p))
      p)
≔ @ind_eql
    Circle_grpd
    circle_base
    (λ x : τ Circle_grpd,
      λ p : τ (@= Circle_grpd circle_base x),
        @=
          (@= Circle_grpd circle_base x)
          (@circle_decode_at x (@circle_encode x p))
          p)
    (@eq_refl
      (@= Circle_grpd circle_base circle_base)
      (@eq_refl Circle_grpd circle_base))
    x
    p;

// Function action preserves path composition propositionally.
symbol circle_eq_ap_trans
  [X Y : Grpd]
  (f : τ X → τ Y)
  [x y : τ X]
  (p : τ (@= X x y))
  [z : τ X]
  (q : τ (@= X y z))
  : τ (@=
      (@= Y (f x) (f z))
      (@eq_ap X Y f x z (@eq_trans X x y z p q))
      (@eq_trans
        Y (f x) (f y) (f z)
        (@eq_ap X Y f x y p)
        (@eq_ap X Y f y z q)))
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @Pi_grpd
        X
        (λ z : τ X,
          @Pi_grpd
            (@= X y z)
            (λ q : τ (@= X y z),
              @=
                (@= Y (f x) (f z))
                (@eq_ap X Y f x z (@eq_trans X x y z p q))
                (@eq_trans
                  Y (f x) (f y) (f z)
                  (@eq_ap X Y f x y p)
                  (@eq_ap X Y f y z q)))))
    (λ z : τ X,
      λ q : τ (@= X y z),
      @eq_refl (@= Y (f y) (f z)) (@eq_ap X Y f y z q))
    x
    p
    z
    q;

// Universe transport respects path composition propositionally.
symbol coe_grpd_trans
  [A B C : Grpd]
  (p : τ (@= Grpd_grpd A B))
  (q : τ (@= Grpd_grpd B C))
  (a : τ A)
  : τ (@= C
      (@coe_grpd
        A C
        (@eq_trans Grpd_grpd A B C p q)
        a)
      (@coe_grpd B C q (@coe_grpd A B p a)))
≔ @ind_eqr
    Grpd_grpd
    B
    (λ A : Grpd,
      λ p : τ (@= Grpd_grpd A B),
        @Pi_grpd Grpd_grpd
          (λ C : Grpd,
            @Pi_grpd
              (@= Grpd_grpd B C)
              (λ q : τ (@= Grpd_grpd B C),
                @Pi_grpd A
                  (λ a : τ A,
                    @= C
                      (@coe_grpd
                        A C
                        (@eq_trans Grpd_grpd A B C p q)
                        a)
                      (@coe_grpd B C q (@coe_grpd A B p a))))))
    (λ C : Grpd,
      λ q : τ (@= Grpd_grpd B C),
        λ b : τ B,
          @eq_refl C (@coe_grpd B C q b))
    A
    p
    C
    q
    a;

// Encoding a composite loop is iterated transport in the Code family.
symbol circle_encode_trans
  (p q : τ (@= Circle_grpd circle_base circle_base))
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p q))
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base q)
        (@circle_encode circle_base p)))
≔ @eq_trans
    Integer_grpd
    (@circle_encode
      circle_base
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        p q))
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_trans
        Grpd_grpd
        Integer_grpd Integer_grpd Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base p)
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base q))
      integer_zero)
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base q)
      (@circle_encode circle_base p))
    (@eq_ap
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      Integer_grpd
      (λ r : τ (@= Grpd_grpd Integer_grpd Integer_grpd),
        @coe_grpd Integer_grpd Integer_grpd r integer_zero)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p q))
      (@eq_trans
        Grpd_grpd
        Integer_grpd Integer_grpd Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base p)
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base q))
      (@circle_eq_ap_trans
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base p
        circle_base q))
    (@coe_grpd_trans
      Integer_grpd Integer_grpd Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base p)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base q)
      integer_zero);

symbol circle_encode_loop_suffix
  (p : τ (@= Circle_grpd circle_base circle_base))
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p circle_loop))
      (integer_succ (@circle_encode circle_base p)))
≔ @eq_trans
    Integer_grpd
    (@circle_encode
      circle_base
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        p circle_loop))
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      (@circle_encode circle_base p))
    (integer_succ (@circle_encode circle_base p))
    (@circle_encode_trans p circle_loop)
    (@circle_Code_transport_loop (@circle_encode circle_base p));

// Function action preserves path reversal propositionally.
symbol circle_eq_ap_sym
  [X Y : Grpd]
  (f : τ X → τ Y)
  [x y : τ X]
  (p : τ (@= X x y))
  : τ (@=
      (@= Y (f y) (f x))
      (@eq_ap X Y f y x (@eq_sym X x y p))
      (@eq_sym Y (f x) (f y) (@eq_ap X Y f x y p)))
≔ @ind_eqr
    X
    y
    (λ x : τ X,
      λ p : τ (@= X x y),
      @=
        (@= Y (f y) (f x))
        (@eq_ap X Y f y x (@eq_sym X x y p))
        (@eq_sym Y (f x) (f y) (@eq_ap X Y f x y p)))
    (@eq_refl
      (@= Y (f y) (f y))
      (@eq_refl Y (f y)))
    x
    p;

// Transport back along an inverse universe path and then forward cancels.
symbol coe_grpd_sym_left
  [A B : Grpd]
  (p : τ (@= Grpd_grpd A B))
  (b : τ B)
  : τ (@= B
      (@coe_grpd
        A B p
        (@coe_grpd
          B A
          (@eq_sym Grpd_grpd A B p)
          b))
      b)
≔ @ind_eqr
    Grpd_grpd
    B
    (λ A : Grpd,
      λ p : τ (@= Grpd_grpd A B),
        @Pi_grpd B
          (λ b : τ B,
            @= B
              (@coe_grpd
                A B p
                (@coe_grpd
                  B A
                  (@eq_sym Grpd_grpd A B p)
                  b))
              b))
    (λ b : τ B, @eq_refl B b)
    A
    p
    b;

// Inverse transport for successor univalence is the selected predecessor.
symbol integer_succ_path_inverse_coe
  (z : τ Integer_grpd)
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_sym
          Grpd_grpd
          Integer_grpd Integer_grpd
          integer_succ_path)
        z)
      (integer_pred z))
≔ @eq_trans
    Integer_grpd
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_sym
        Grpd_grpd
        Integer_grpd Integer_grpd
        integer_succ_path)
      z)
    (integer_pred
      (integer_succ
        (@coe_grpd
          Integer_grpd
          Integer_grpd
          (@eq_sym
            Grpd_grpd
            Integer_grpd Integer_grpd
            integer_succ_path)
          z)))
    (integer_pred z)
    (@eq_sym
      Integer_grpd
      (integer_pred
        (integer_succ
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            (@eq_sym
              Grpd_grpd
              Integer_grpd Integer_grpd
              integer_succ_path)
            z)))
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_sym
          Grpd_grpd
          Integer_grpd Integer_grpd
          integer_succ_path)
        z)
      (@integer_pred_succ
        (@coe_grpd
          Integer_grpd
          Integer_grpd
          (@eq_sym
            Grpd_grpd
            Integer_grpd Integer_grpd
            integer_succ_path)
          z)))
    (@eq_trans
      Integer_grpd
      (integer_pred
        (integer_succ
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            (@eq_sym
              Grpd_grpd
              Integer_grpd Integer_grpd
              integer_succ_path)
            z)))
      (integer_pred
        (@coe_grpd
          Integer_grpd
          Integer_grpd
          integer_succ_path
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            (@eq_sym
              Grpd_grpd
              Integer_grpd Integer_grpd
              integer_succ_path)
            z)))
      (integer_pred z)
      (@eq_ap
        Integer_grpd Integer_grpd
        integer_pred
        (integer_succ
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            (@eq_sym
              Grpd_grpd
              Integer_grpd Integer_grpd
              integer_succ_path)
            z))
        (@coe_grpd
          Integer_grpd
          Integer_grpd
          integer_succ_path
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            (@eq_sym
              Grpd_grpd
              Integer_grpd Integer_grpd
              integer_succ_path)
            z))
        (@eq_sym
          Integer_grpd
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            integer_succ_path
            (@coe_grpd
              Integer_grpd
              Integer_grpd
              (@eq_sym
                Grpd_grpd
                Integer_grpd Integer_grpd
                integer_succ_path)
              z))
          (integer_succ
            (@coe_grpd
              Integer_grpd
              Integer_grpd
              (@eq_sym
                Grpd_grpd
                Integer_grpd Integer_grpd
                integer_succ_path)
              z))
          (@integer_succ_path_coe
            (@coe_grpd
              Integer_grpd
              Integer_grpd
              (@eq_sym
                Grpd_grpd
                Integer_grpd Integer_grpd
                integer_succ_path)
              z))))
      (@eq_ap
        Integer_grpd Integer_grpd
        integer_pred
        (@coe_grpd
          Integer_grpd
          Integer_grpd
          integer_succ_path
          (@coe_grpd
            Integer_grpd
            Integer_grpd
            (@eq_sym
              Grpd_grpd
              Integer_grpd Integer_grpd
              integer_succ_path)
            z))
        z
        (@coe_grpd_sym_left
          Integer_grpd Integer_grpd
          integer_succ_path
          z)));

// The inverse Circle generator acts on Code by inverse successor transport.
symbol circle_Code_beta_loop_inverse
  : τ (@=
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop_inverse)
      (@eq_sym
        Grpd_grpd
        Integer_grpd Integer_grpd
        integer_succ_path))
≔ @eq_trans
    (@= Grpd_grpd Integer_grpd Integer_grpd)
    (@eq_ap
      Circle_grpd Grpd_grpd
      CircleCode
      circle_base circle_base circle_loop_inverse)
    (@eq_sym
      Grpd_grpd
      Integer_grpd Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop))
    (@eq_sym
      Grpd_grpd
      Integer_grpd Integer_grpd
      integer_succ_path)
    (@circle_eq_ap_sym
      Circle_grpd Grpd_grpd
      CircleCode
      circle_base circle_base circle_loop)
    (@eq_ap
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      (λ r : τ (@= Grpd_grpd Integer_grpd Integer_grpd),
        @eq_sym Grpd_grpd Integer_grpd Integer_grpd r)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      integer_succ_path
      circle_Code_beta_loop);

// Code transport around the inverse generator is Integer predecessor.
symbol circle_Code_transport_loop_inverse
  (z : τ Integer_grpd)
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop_inverse)
        z)
      (integer_pred z))
≔ @eq_trans
    Integer_grpd
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop_inverse)
      z)
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_sym
        Grpd_grpd
        Integer_grpd Integer_grpd
        integer_succ_path)
      z)
    (integer_pred z)
    (@eq_ap
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      Integer_grpd
      (λ q : τ (@= Grpd_grpd Integer_grpd Integer_grpd),
        @coe_grpd Integer_grpd Integer_grpd q z)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop_inverse)
      (@eq_sym
        Grpd_grpd
        Integer_grpd Integer_grpd
        integer_succ_path)
      circle_Code_beta_loop_inverse)
    (@integer_succ_path_inverse_coe z);

symbol circle_encode_loop_inverse_suffix
  (p : τ (@= Circle_grpd circle_base circle_base))
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p circle_loop_inverse))
      (integer_pred (@circle_encode circle_base p)))
≔ @eq_trans
    Integer_grpd
    (@circle_encode
      circle_base
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        p circle_loop_inverse))
    (@coe_grpd
      Integer_grpd
      Integer_grpd
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop_inverse)
      (@circle_encode circle_base p))
    (integer_pred (@circle_encode circle_base p))
    (@circle_encode_trans p circle_loop_inverse)
    (@circle_Code_transport_loop_inverse (@circle_encode circle_base p));

// Positive loop powers encode as the canonical nonnegative integers.
symbol circle_encode_nat_power
  (n : τ Nat_grpd)
  : τ (@= Integer_grpd
      (@circle_encode circle_base (circle_nat_power n))
      (integer_of_nat n))
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @= Integer_grpd
        (@circle_encode circle_base (circle_nat_power n))
        (integer_of_nat n))
    circle_encode_refl
    (λ n : τ Nat_grpd,
      λ ih : τ (@= Integer_grpd
        (@circle_encode circle_base (circle_nat_power n))
        (integer_of_nat n)),
      @eq_trans
        Integer_grpd
        (@circle_encode
          circle_base
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (circle_nat_power n)
            circle_loop))
        (integer_succ
          (@circle_encode circle_base (circle_nat_power n)))
        (integer_of_nat (succ n))
        (@circle_encode_loop_suffix (circle_nat_power n))
        (@eq_ap
          Integer_grpd Integer_grpd
          integer_succ
          (@circle_encode circle_base (circle_nat_power n))
          (integer_of_nat n)
          ih))
    n;

// Negative loop powers encode as the zero element at their telescope stage.
symbol circle_encode_nat_inverse_power
  (n : τ Nat_grpd)
  : τ (@= Integer_grpd
      (@circle_encode circle_base (circle_nat_inverse_power n))
      (integer_stage n zero))
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @= Integer_grpd
        (@circle_encode circle_base (circle_nat_inverse_power n))
        (integer_stage n zero))
    circle_encode_refl
    (λ n : τ Nat_grpd,
      λ ih : τ (@= Integer_grpd
        (@circle_encode circle_base (circle_nat_inverse_power n))
        (integer_stage n zero)),
      @eq_trans
        Integer_grpd
        (@circle_encode
          circle_base
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (circle_nat_inverse_power n)
            circle_loop_inverse))
        (integer_pred
          (@circle_encode circle_base (circle_nat_inverse_power n)))
        (integer_stage (succ n) zero)
        (@circle_encode_loop_inverse_suffix
          (circle_nat_inverse_power n))
        (@eq_ap
          Integer_grpd Integer_grpd
          integer_pred
          (@circle_encode circle_base (circle_nat_inverse_power n))
          (integer_stage n zero)
          ih))
    n;

// Every simultaneously cancelling stage power encodes to its Integer stage.
symbol circle_encode_integer_stage_power
  (n x : τ Nat_grpd)
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (circle_integer_stage_power n x))
      (integer_stage n x))
≔ (@nat_elim
      (λ n : τ Nat_grpd,
        @Pi_grpd
          Nat_grpd
          (λ x : τ Nat_grpd,
            @= Integer_grpd
              (@circle_encode
                circle_base
                (circle_integer_stage_power n x))
              (integer_stage n x)))
      (λ x : τ Nat_grpd,
        @circle_encode_nat_power x)
      (λ n : τ Nat_grpd,
        λ previous : τ (@Pi_grpd
          Nat_grpd
          (λ x : τ Nat_grpd,
            @= Integer_grpd
              (@circle_encode
                circle_base
                (circle_integer_stage_power n x))
              (integer_stage n x))),
        λ x : τ Nat_grpd,
          @nat_elim
            (λ x : τ Nat_grpd,
              @= Integer_grpd
                (@circle_encode
                  circle_base
                  (circle_integer_stage_power (succ n) x))
                (integer_stage (succ n) x))
            (@circle_encode_nat_inverse_power (succ n))
            (λ x0 : τ Nat_grpd,
              λ _ : τ (@= Integer_grpd
                (@circle_encode
                  circle_base
                  (circle_integer_stage_power (succ n) x0))
                (integer_stage (succ n) x0)),
              @eq_trans
                Integer_grpd
                (@circle_encode
                  circle_base
                  (circle_integer_stage_power n x0))
                (integer_stage n x0)
                (integer_stage (succ n) (succ x0))
                (previous x0)
                (@eq_sym
                  Integer_grpd
                  (integer_stage (succ n) (succ x0))
                  (integer_stage n x0)
                  (@integer_stage_step n x0)))
            x)
      n)
    x;

// Based code-side inverse motive: encode after the based decoder is identity.
symbol CircleEncodeDecodeBaseMotive
  (z : τ Integer_grpd)
  : Grpd
≔ @= Integer_grpd
    (@circle_encode circle_base (circle_decode z))
    z;

symbol circle_encode_decode_base_motive_is_prop
  (z : τ Integer_grpd)
  : τ (IsPropGrpd (CircleEncodeDecodeBaseMotive z))
≔ integer_is_set
    (@circle_encode circle_base (circle_decode z))
    z;

symbol circle_encode_decode_base_motive_is_set
  (z : τ Integer_grpd)
  : τ (IsSetGrpd (CircleEncodeDecodeBaseMotive z))
≔ @is_trunc_grpd_succ
    trunc_minus_one
    (CircleEncodeDecodeBaseMotive z)
    (circle_encode_decode_base_motive_is_prop z);

symbol circle_encode_decode_base_stage
  (n x : τ Nat_grpd)
  : τ (CircleEncodeDecodeBaseMotive (integer_stage n x))
≔ @circle_encode_integer_stage_power n x;

symbol circle_encode_decode_base_stage_coherence
  (n x : τ Nat_grpd)
  : τ (@PathOver
      Integer_grpd
      CircleEncodeDecodeBaseMotive
      (integer_stage (succ n) (succ x))
      (integer_stage n x)
      (integer_stage_step n x)
      (circle_encode_decode_base_stage (succ n) (succ x))
      (circle_encode_decode_base_stage n x))
≔ @prop_family_pathover
    Integer_grpd
    CircleEncodeDecodeBaseMotive
    circle_encode_decode_base_motive_is_prop
    (integer_stage (succ n) (succ x))
    (integer_stage n x)
    (integer_stage_step n x)
    (circle_encode_decode_base_stage (succ n) (succ x))
    (circle_encode_decode_base_stage n x);

// Encode after the based decoder is propositionally the identity on Integer.
symbol circle_encode_decode_base
  (z : τ Integer_grpd)
  : τ (CircleEncodeDecodeBaseMotive z)
≔ @integer_ind
    CircleEncodeDecodeBaseMotive
    circle_encode_decode_base_motive_is_set
    circle_encode_decode_base_stage
    circle_encode_decode_base_stage_coherence
    z;

// Every fibre of the Circle code family is a set.
symbol CircleCodeSetMotive
  (x : τ Circle_grpd)
  : Grpd
≔ IsSetGrpd (CircleCode x);

symbol circle_Code_set_motive_is_prop
  (x : τ Circle_grpd)
  : τ (IsPropGrpd (CircleCodeSetMotive x))
≔ @is_trunc_grpd_evidence_is_prop
    trunc_zero
    (CircleCode x);

symbol circle_Code_set_loop_coherence
  : τ (@PathOver
      Circle_grpd
      CircleCodeSetMotive
      circle_base circle_base circle_loop
      integer_is_set integer_is_set)
≔ @prop_family_pathover
    Circle_grpd
    CircleCodeSetMotive
    circle_Code_set_motive_is_prop
    circle_base circle_base circle_loop
    integer_is_set integer_is_set;

symbol circle_Code_is_set
  (x : τ Circle_grpd)
  : τ (IsSetGrpd (CircleCode x))
≔ @circle_ind
    CircleCodeSetMotive
    integer_is_set
    circle_Code_set_loop_coherence
    x;

// Fibrewise code-side inverse for the endpoint-dependent decoder.
symbol CircleEncodeDecodeMotive
  (x : τ Circle_grpd)
  : Grpd
≔ @Pi_grpd
    (CircleCode x)
    (λ c : τ (CircleCode x),
      @= (CircleCode x)
        (@circle_encode x (@circle_decode_at x c))
        c);

symbol circle_encode_decode_motive_is_prop
  (x : τ Circle_grpd)
  : τ (IsPropGrpd (CircleEncodeDecodeMotive x))
≔ @is_prop_pi
    (CircleCode x)
    (λ c : τ (CircleCode x),
      @= (CircleCode x)
        (@circle_encode x (@circle_decode_at x c))
        c)
    (λ c : τ (CircleCode x),
      circle_Code_is_set
        x
        (@circle_encode x (@circle_decode_at x c))
        c);

symbol circle_encode_decode_loop_coherence
  : τ (@PathOver
      Circle_grpd
      CircleEncodeDecodeMotive
      circle_base circle_base circle_loop
      circle_encode_decode_base circle_encode_decode_base)
≔ @prop_family_pathover
    Circle_grpd
    CircleEncodeDecodeMotive
    circle_encode_decode_motive_is_prop
    circle_base circle_base circle_loop
    circle_encode_decode_base circle_encode_decode_base;

symbol circle_encode_decode_function
  (x : τ Circle_grpd)
  : τ (CircleEncodeDecodeMotive x)
≔ @circle_ind
    CircleEncodeDecodeMotive
    circle_encode_decode_base
    circle_encode_decode_loop_coherence
    x;

// Encode after the endpoint decoder is propositionally identity in every Code fibre.
symbol circle_encode_decode
  [x : τ Circle_grpd]
  (c : τ (CircleCode x))
  : τ (@= (CircleCode x)
      (@circle_encode x (@circle_decode_at x c))
      c)
≔ circle_encode_decode_function x c;

// Categorical realization of the intrinsic groupoidal Circle.
symbol Circle_cat : Cat
≔ Path_cat Circle_grpd;

symbol circle_cat_is_groupoidal
  : τ (IsGroupoidalCat Circle_cat)
≔ @path_cat_is_groupoidal Circle_grpd;

// Selected maps underlying the based-loop/Integer equivalence.
symbol circle_loop_encode_function
  : τ (@Function_grpd
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd)
≔ λ p : τ (@= Circle_grpd circle_base circle_base),
    @circle_encode circle_base p;

symbol circle_loop_decode_function
  : τ (@Function_grpd
      Integer_grpd
      (@= Circle_grpd circle_base circle_base))
≔ circle_decode;

// The two semantic round trips form explicit quasi-inverse data.
symbol circle_loop_integer_by_inverse
  : τ (@EquivByInverse
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd
      circle_loop_encode_function
      circle_loop_decode_function)
≔ @Struct_sigma
    (@Pi_grpd
      (@= Circle_grpd circle_base circle_base)
      (λ p : τ (@= Circle_grpd circle_base circle_base),
        @= (@= Circle_grpd circle_base circle_base)
          (circle_loop_decode_function (circle_loop_encode_function p))
          p))
    (λ _ : τ (@Pi_grpd
      (@= Circle_grpd circle_base circle_base)
      (λ p : τ (@= Circle_grpd circle_base circle_base),
        @= (@= Circle_grpd circle_base circle_base)
          (circle_loop_decode_function (circle_loop_encode_function p))
          p)),
      @Pi_grpd
        Integer_grpd
        (λ z : τ Integer_grpd,
          @= Integer_grpd
            (circle_loop_encode_function (circle_loop_decode_function z))
            z))
    (λ p : τ (@= Circle_grpd circle_base circle_base),
      @circle_decode_encode circle_base p)
    circle_encode_decode_base;

// Based loop space of the Circle is equivalent to the Integer line.
symbol circle_loop_integer_type_equiv
  : τ (TypeEquiv
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd)
≔ @Struct_sigma
    (@Function_grpd
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd)
    (λ map : τ (@Function_grpd
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd),
      @IsEquivMap
        (@= Circle_grpd circle_base circle_base)
        Integer_grpd
        map)
    circle_loop_encode_function
    (@is_equiv_map_by_inverse
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd
      circle_loop_encode_function
      circle_loop_decode_function
      circle_loop_integer_by_inverse);

// The categorical Hom carrier is definitionally the same based loop space.
symbol circle_hom_integer_type_equiv
  : τ (TypeEquiv
      (Hom Circle_cat circle_base circle_base)
      Integer_grpd)
≔ circle_loop_integer_type_equiv;

// Equality-valued facade for the carrier equivalence in Grpd_cat.
symbol circle_loop_integer_omega_equiv
  : τ (@OmegaEquiv
      Grpd_cat
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd)
≔ @type_equiv_to_omega
    (@= Circle_grpd circle_base circle_base)
    Integer_grpd
    circle_loop_integer_type_equiv;

// Whole Path-category action of the selected encoder.
symbol circle_hom_integer_func
  : τ (Functor
      (Hom_cat Circle_cat circle_base circle_base)
      (Path_cat Integer_grpd))
≔ @path_map_func
    (@= Circle_grpd circle_base circle_base)
    Integer_grpd
    circle_loop_encode_function;

// Functoriality transports the Grpd equivalence to the categorical Hom.
symbol circle_hom_integer_cat_evidence
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat Circle_cat circle_base circle_base)
      (Path_cat Integer_grpd)
      circle_hom_integer_func)
≔ @omega_equiv_along_fapp1_fapp0
    Grpd_cat
    Cat_cat
    Path_cat_func
    (@= Circle_grpd circle_base circle_base)
    Integer_grpd
    circle_loop_encode_function
    (@omega_equiv_evidence
      Grpd_cat
      (@= Circle_grpd circle_base circle_base)
      Integer_grpd
      circle_loop_integer_omega_equiv);

symbol circle_hom_integer_cat_omega_equiv
  : τ (@OmegaEquiv
      Cat_cat
      (Hom_cat Circle_cat circle_base circle_base)
      (Path_cat Integer_grpd))
≔ @omega_equiv_pack
    Cat_cat
    (Hom_cat Circle_cat circle_base circle_base)
    (Path_cat Integer_grpd)
    circle_hom_integer_func
    circle_hom_integer_cat_evidence;

// Signature dimension and the computed carrier equivalence give independent sethood evidence.
symbol circle_hom_is_set_from_dimension
  : τ (IsSetGrpd
      (Hom Circle_cat circle_base circle_base))
≔ circle_loop_space_is_set;

symbol circle_hom_is_set_from_equiv
  : τ (IsSetGrpd
      (Hom Circle_cat circle_base circle_base))
≔ @is_trunc_grpd_equiv_from
    trunc_zero
    (Hom Circle_cat circle_base circle_base)
    Integer_grpd
    circle_hom_integer_type_equiv
    integer_is_set;

// The Circle's one-type signature makes its path category locally set-valued.
symbol circle_cat_is_locally_set
  : τ (IsLocallySetCat Circle_cat)
≔ λ x : τ Circle_grpd,
    λ y : τ Circle_grpd,
      circle_is_groupoid x y;
