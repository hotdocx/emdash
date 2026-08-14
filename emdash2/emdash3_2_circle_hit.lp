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

// Categorical realization of the intrinsic groupoidal Circle.
symbol Circle_cat : Cat
≔ Path_cat Circle_grpd;

symbol circle_cat_is_groupoidal
  : τ (IsGroupoidalCat Circle_cat)
≔ @path_cat_is_groupoidal Circle_grpd;
