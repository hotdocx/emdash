/*
  Focused reviewer for the Circle HIT signature, Integer universal cover,
  endpoint-dependent decoder, and both encode/decode inverse laws.
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

// Natural and inverse powers use the conventional right-appending recursion.
assert ⊢ circle_nat_power zero
  ≡ @eq_refl Circle_grpd circle_base;

assert (n : τ Nat_grpd) ⊢
  circle_nat_power (succ n)
  ≡ @eq_trans
      Circle_grpd
      circle_base circle_base circle_base
      (circle_nat_power n) circle_loop;

assert ⊢ circle_nat_inverse_power (succ zero)
  ≡ circle_loop_inverse;

// Simultaneous cancellation makes the telescope step judgmental.
assert (x : τ Nat_grpd) ⊢
  circle_integer_stage_power zero x
  ≡ circle_nat_power x;

assert (n : τ Nat_grpd) ⊢
  circle_integer_stage_power (succ n) zero
  ≡ circle_nat_inverse_power (succ n);

assert (n x : τ Nat_grpd) ⊢
  circle_integer_stage_power (succ n) (succ x)
  ≡ circle_integer_stage_power n x;

assert (n x : τ Nat_grpd) ⊢
  circle_integer_stage_power_step n x
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_integer_stage_power (succ n) (succ x))
      (circle_integer_stage_power n x));

// Integer elimination yields a computational based decoder.
assert (n x : τ Nat_grpd) ⊢
  circle_decode (integer_stage n x)
  ≡ circle_integer_stage_power n x;

assert ⊢ circle_decode integer_zero
  ≡ @eq_refl Circle_grpd circle_base;

assert (n : τ Nat_grpd) ⊢
  circle_decode (integer_of_nat n)
  ≡ circle_nat_power n;

assert ⊢ circle_decode (integer_of_nat (succ zero))
  ≡ circle_loop;

assert ⊢ circle_decode integer_neg_one
  ≡ circle_loop_inverse;

assertnot (z : τ Integer_grpd) ⊢
  circle_decode z
  ≡ @eq_refl Circle_grpd circle_base;

// Successor compatibility is proved from the cancelling stage presentation.
assert (n x : τ Nat_grpd) ⊢
  circle_integer_stage_power_succ n x
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_integer_stage_power n (succ x))
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        (circle_integer_stage_power n x)
        circle_loop));

assert (z : τ Integer_grpd) ⊢ circle_decode_succ z
  : τ (@=
      (@= Circle_grpd circle_base circle_base)
      (circle_decode (integer_succ z))
      (@eq_trans
        Circle_grpd
        circle_base circle_base circle_base
        (circle_decode z)
        circle_loop));

assert (z : τ Integer_grpd) ⊢ circle_Code_transport_loop z
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop)
        z)
      (integer_succ z));

// The based decoder supplies the exact dependent loop coherence for Circle J.
assert ⊢ circle_decode_loop_coherence
  : τ (@PathOver
      Circle_grpd
      CircleDecodeMotive
      circle_base circle_base circle_loop
      circle_decode circle_decode);

assert (x : τ Circle_grpd) ⊢
  circle_decode_function x
  : τ (CircleDecodeMotive x);

assert (z : τ Integer_grpd) ⊢
  @circle_decode_at circle_base z
  ≡ circle_decode z;

assert ⊢ circle_decode_function_beta_loop
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
      circle_decode_loop_coherence);

// The path-side inverse is endpoint-general, not only a based-loop statement.
assert [x : τ Circle_grpd]
  (p : τ (@= Circle_grpd circle_base x)) ⊢
  @circle_decode_encode x p
  : τ (@=
      (@= Circle_grpd circle_base x)
      (@circle_decode_at x (@circle_encode x p))
      p);

// Code action follows successor on the generator and predecessor on its inverse.
assert (z : τ Integer_grpd) ⊢ circle_Code_transport_loop_inverse z
  : τ (@= Integer_grpd
      (@coe_grpd
        Integer_grpd
        Integer_grpd
        (@eq_ap
          Circle_grpd Grpd_grpd
          CircleCode
          circle_base circle_base circle_loop_inverse)
        z)
      (integer_pred z));

assert (p : τ (@= Circle_grpd circle_base circle_base)) ⊢
  circle_encode_loop_suffix p
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p circle_loop))
      (integer_succ (@circle_encode circle_base p)));

assert (p : τ (@= Circle_grpd circle_base circle_base)) ⊢
  circle_encode_loop_inverse_suffix p
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (@eq_trans
          Circle_grpd
          circle_base circle_base circle_base
          p circle_loop_inverse))
      (integer_pred (@circle_encode circle_base p)));

// The two axes and every telescope representative encode to their Integer values.
assert (n : τ Nat_grpd) ⊢ circle_encode_nat_power n
  : τ (@= Integer_grpd
      (@circle_encode circle_base (circle_nat_power n))
      (integer_of_nat n));

assert (n : τ Nat_grpd) ⊢ circle_encode_nat_inverse_power n
  : τ (@= Integer_grpd
      (@circle_encode circle_base (circle_nat_inverse_power n))
      (integer_stage n zero));

assert (n x : τ Nat_grpd) ⊢ circle_encode_integer_stage_power n x
  : τ (@= Integer_grpd
      (@circle_encode
        circle_base
        (circle_integer_stage_power n x))
      (integer_stage n x));

// The code-side inverse is first proved at the base, then over every fibre.
assert (z : τ Integer_grpd) ⊢ circle_encode_decode_base z
  : τ (@= Integer_grpd
      (@circle_encode circle_base (circle_decode z))
      z);

assert (x : τ Circle_grpd) ⊢ circle_Code_is_set x
  : τ (IsSetGrpd (CircleCode x));

assert [x : τ Circle_grpd]
  (c : τ (CircleCode x)) ⊢
  @circle_encode_decode x c
  : τ (@= (CircleCode x)
      (@circle_encode x (@circle_decode_at x c))
      c);

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
