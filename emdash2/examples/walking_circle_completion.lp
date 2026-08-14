/*
  Focused reviewer for the concrete WalkingEnd-to-Circle comparison. It checks
  constructor action, compatibility of every Nat power, and the commuting
  encoder square without claiming a generic groupoidification reflector.
*/

require open emdash.emdash3_2_walking_circle_completion;

assert ⊢ walking_to_circle_func
  : τ (Functor WalkingEnd_cat Circle_cat);

assert ⊢
  @fapp0
    WalkingEnd_cat Circle_cat
    walking_to_circle_func
    walking_base
  ≡ circle_base;

assert ⊢ walking_to_circle_beta_base
  : τ (@= Circle_grpd
      (@fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base)
      circle_base);

assert ⊢
  @fapp1_fapp0
    WalkingEnd_cat Circle_cat
    walking_to_circle_func
    walking_base walking_base walking_loop
  ≡ circle_loop;

assert ⊢ walking_to_circle_beta_loop
  : τ (@=
      (Hom Circle_cat circle_base circle_base)
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base walking_loop)
      circle_loop);

// Directed powers become exactly the nonnegative Circle powers propositionally.
assert (n : τ Nat_grpd) ⊢ walking_to_circle_power n
  : τ (@=
      (Hom Circle_cat circle_base circle_base)
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base
        (walking_power n))
      (circle_nat_power n));

assert (n : τ Nat_grpd) ⊢ walking_to_circle_power_encode n
  : τ (@= Integer_grpd
      (circle_loop_encode_function
        (@fapp1_fapp0
          WalkingEnd_cat Circle_cat
          walking_to_circle_func
          walking_base walking_base
          (walking_power n)))
      (integer_of_nat n));

// An arbitrary walking endomorphism gives a commuting encoder square.
assert (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  walking_circle_encode_square_point p
  : τ (@= Integer_grpd
      (walking_circle_direct_encode_function p)
      (walking_circle_via_nat_function p));

assert ⊢ walking_circle_encode_square
  : τ (@=
      (@Function_grpd
        (Hom WalkingEnd_cat walking_base walking_base)
        Integer_grpd)
      walking_circle_direct_encode_function
      walking_circle_via_nat_function);

// The comparison is proof-backed; it does not normalize an arbitrary arrow.
assertnot (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @fapp1_fapp0
    WalkingEnd_cat Circle_cat
    walking_to_circle_func
    walking_base walking_base p
  ≡ circle_nat_power (walking_encode_function p);
