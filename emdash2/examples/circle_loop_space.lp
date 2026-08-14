/*
  Focused reviewer for the first Circle HIT signature: constructors,
  one-dimensional evidence, dependent/ordinary point computation, and the
  propositional loop beta. Integer encode/decode is added in the next tranche.
*/

require open emdash.emdash3_2_circle_hit;

assert ⊢ Circle_grpd : Grpd;

assert ⊢ circle_base : τ Circle_grpd;

assert ⊢ circle_loop
  : τ (@= Circle_grpd circle_base circle_base);

assert ⊢ circle_loop_inverse
  : τ (@= Circle_grpd circle_base circle_base);

assert ⊢ circle_is_groupoid
  : τ (IsGroupoidGrpd Circle_grpd);

assert ⊢ circle_loop_space_is_set
  : τ (IsSetGrpd (@= Circle_grpd circle_base circle_base));

assert (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b)) ⊢
  @circle_ind D b ell circle_base
  ≡ b;

assert (D : τ Circle_grpd → Grpd)
  (b : τ (D circle_base))
  (ell : τ (@PathOver
      Circle_grpd D
      circle_base circle_base circle_loop b b)) ⊢
  @circle_ind_beta_loop D b ell
  : τ (@=
      (@PathOver
        Circle_grpd D
        circle_base circle_base circle_loop b b)
      (@eq_apd
        Circle_grpd D
        (λ x : τ Circle_grpd, @circle_ind D b ell x)
        circle_base circle_base circle_loop)
      ell);

assert [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b)) ⊢
  @circle_rec B b ell circle_base
  ≡ b;

assert [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b)) ⊢
  @circle_rec_beta_loop B b ell
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
        circle_base circle_base b b circle_loop ell));

assert [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b)) ⊢
  @circle_rec_beta_loop_path B b ell
  : τ (@=
      (@= B b b)
      (@eq_ap
        Circle_grpd B
        (λ x : τ Circle_grpd, @circle_rec B b ell x)
        circle_base circle_base circle_loop)
      ell);

// The universal-cover fibre and its selected monodromy.
assert (x : τ Circle_grpd) ⊢ CircleCode x : Grpd;

assert ⊢ CircleCode circle_base
  ≡ Integer_grpd;

assert ⊢ circle_Code_beta_loop
  : τ (@=
      (@= Grpd_grpd Integer_grpd Integer_grpd)
      (@eq_ap
        Circle_grpd Grpd_grpd
        CircleCode
        circle_base circle_base circle_loop)
      integer_succ_path);

// Encoding computes at reflexivity and follows successor monodromy on loop.
assert ⊢ @circle_encode
    circle_base
    (@eq_refl Circle_grpd circle_base)
  ≡ integer_zero;

assert ⊢ circle_encode_loop
  : τ (@= Integer_grpd
      (@circle_encode circle_base circle_loop)
      (integer_succ integer_zero));

// An open path has no additional global transport fold.
assertnot (p : τ (@= Circle_grpd circle_base circle_base)) ⊢
  @circle_encode circle_base p
  ≡ integer_zero;

// Only the base constructor computes; an open Circle point stays opaque.
assertnot [B : Grpd]
  (b : τ B)
  (ell : τ (@= B b b))
  (x : τ Circle_grpd) ⊢
  @circle_rec B b ell x
  ≡ b;

assert ⊢ Circle_cat : Cat;

assert ⊢ Obj Circle_cat
  ≡ Circle_grpd;

assert ⊢ Hom Circle_cat circle_base circle_base
  ≡ @= Circle_grpd circle_base circle_base;

assert ⊢ circle_cat_is_groupoidal
  : τ (IsGroupoidalCat Circle_cat);
