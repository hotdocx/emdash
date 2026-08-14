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

/*
  Path-constructor computation is propositional signature data. Its classifier
  retains the full PathOver proof rather than rewriting generic eq_apd.
*/
constant symbol circle_ind_beta_loop
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
      ell);

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

// Propositional loop beta retained in its canonical dependent-path form.
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

// Categorical realization of the intrinsic groupoidal Circle.
symbol Circle_cat : Cat
≔ Path_cat Circle_grpd;

symbol circle_cat_is_groupoidal
  : τ (IsGroupoidalCat Circle_cat)
≔ @path_cat_is_groupoidal Circle_grpd;
