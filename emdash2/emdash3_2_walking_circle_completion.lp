/*
  Concrete directed-to-groupoidal comparison from WalkingEnd to Circle.

  The walking recursor sends the unique object and directed generator to the
  Circle base and loop. Nat induction then proves that its action on every
  established walking power is the corresponding nonnegative Circle power.
  This is computational group-completion evidence for the selected example;
  it does not construct a generic groupoidification reflector or adjunction.
*/

require open emdash.emdash3_2_walking_end_hit;
require open emdash.emdash3_2_circle_hit;

// The concrete comparison sends the walking generator to the Circle loop.
symbol walking_to_circle_func
  : τ (Functor WalkingEnd_cat Circle_cat)
≔ @walking_end_rec_func Circle_cat circle_base circle_loop;

symbol walking_to_circle_beta_base
  : τ (@= Circle_grpd
      (@fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base)
      circle_base)
≔ @walking_end_rec_beta_base
    Circle_cat circle_base circle_loop;

symbol walking_to_circle_beta_loop
  : τ (@=
      (Hom Circle_cat circle_base circle_base)
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base walking_loop)
      circle_loop)
≔ @walking_end_rec_beta_loop_ordinary
    Circle_cat circle_base circle_loop;

// Every directed Nat power maps to the matching nonnegative Circle power.
symbol walking_to_circle_power
  (n : τ Nat_grpd)
  : τ (@=
      (Hom Circle_cat circle_base circle_base)
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base
        (walking_power n))
      (circle_nat_power n))
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @=
        (Hom Circle_cat circle_base circle_base)
        (@fapp1_fapp0
          WalkingEnd_cat Circle_cat
          walking_to_circle_func
          walking_base walking_base
          (walking_power n))
        (circle_nat_power n))
    (@eq_refl
      (Hom Circle_cat circle_base circle_base)
      (@eq_refl Circle_grpd circle_base))
    (λ n : τ Nat_grpd,
      λ ih : τ (@=
        (Hom Circle_cat circle_base circle_base)
        (@fapp1_fapp0
          WalkingEnd_cat Circle_cat
          walking_to_circle_func
          walking_base walking_base
          (walking_power n))
        (circle_nat_power n)),
      @eq_trans
        (Hom Circle_cat circle_base circle_base)
        (@fapp1_fapp0
          WalkingEnd_cat Circle_cat
          walking_to_circle_func
          walking_base walking_base
          (walking_power (succ n)))
        (@comp_fapp0
          Circle_cat
          circle_base circle_base circle_base
          circle_loop
          (@fapp1_fapp0
            WalkingEnd_cat Circle_cat
            walking_to_circle_func
            walking_base walking_base
            (walking_power n)))
        (circle_nat_power (succ n))
        (@walking_end_rec_loop_prefix_eq
          Circle_cat
          circle_base
          circle_loop
          (walking_power n))
        (@eq_trans
          (Hom Circle_cat circle_base circle_base)
          (@comp_fapp0
            Circle_cat
            circle_base circle_base circle_base
            circle_loop
            (@fapp1_fapp0
              WalkingEnd_cat Circle_cat
              walking_to_circle_func
              walking_base walking_base
              (walking_power n)))
          (@eq_trans
            Circle_grpd
            circle_base circle_base circle_base
            (@fapp1_fapp0
              WalkingEnd_cat Circle_cat
              walking_to_circle_func
              walking_base walking_base
              (walking_power n))
            circle_loop)
          (circle_nat_power (succ n))
          (@path_comp_eq_trans
            Circle_grpd
            circle_base circle_base
            (@fapp1_fapp0
              WalkingEnd_cat Circle_cat
              walking_to_circle_func
              walking_base walking_base
              (walking_power n))
            circle_base
            circle_loop)
          (@eq_ap
            (Hom Circle_cat circle_base circle_base)
            (Hom Circle_cat circle_base circle_base)
            (λ p : τ (Hom Circle_cat circle_base circle_base),
              @eq_trans
                Circle_grpd
                circle_base circle_base circle_base
                p circle_loop)
            (@fapp1_fapp0
              WalkingEnd_cat Circle_cat
              walking_to_circle_func
              walking_base walking_base
              (walking_power n))
            (circle_nat_power n)
            ih)))
    n;

// Encoding the image of a walking power is the canonical Nat-to-Integer inclusion.
symbol walking_to_circle_power_encode
  (n : τ Nat_grpd)
  : τ (@= Integer_grpd
      (circle_loop_encode_function
        (@fapp1_fapp0
          WalkingEnd_cat Circle_cat
          walking_to_circle_func
          walking_base walking_base
          (walking_power n)))
      (integer_of_nat n))
≔ @eq_trans
    Integer_grpd
    (circle_loop_encode_function
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base
        (walking_power n)))
    (circle_loop_encode_function (circle_nat_power n))
    (integer_of_nat n)
    (@eq_ap
      (Hom Circle_cat circle_base circle_base)
      Integer_grpd
      circle_loop_encode_function
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base
        (walking_power n))
      (circle_nat_power n)
      (@walking_to_circle_power n))
    (@circle_encode_nat_power n);

// Compare the two routes from a walking endomorphism to Integer.
symbol walking_circle_direct_encode_function
  : τ (@Function_grpd
      (Hom WalkingEnd_cat walking_base walking_base)
      Integer_grpd)
≔ λ p : τ (Hom WalkingEnd_cat walking_base walking_base),
    circle_loop_encode_function
      (@fapp1_fapp0
        WalkingEnd_cat Circle_cat
        walking_to_circle_func
        walking_base walking_base p);

symbol walking_circle_via_nat_function
  : τ (@Function_grpd
      (Hom WalkingEnd_cat walking_base walking_base)
      Integer_grpd)
≔ λ p : τ (Hom WalkingEnd_cat walking_base walking_base),
    integer_of_nat (walking_encode_function p);

symbol walking_circle_encode_square_point
  (p : τ (Hom WalkingEnd_cat walking_base walking_base))
  : τ (@= Integer_grpd
      (walking_circle_direct_encode_function p)
      (walking_circle_via_nat_function p))
≔ @eq_trans
    Integer_grpd
    (walking_circle_direct_encode_function p)
    (walking_circle_direct_encode_function
      (walking_power (walking_encode_function p)))
    (walking_circle_via_nat_function p)
    (@eq_ap
      (Hom WalkingEnd_cat walking_base walking_base)
      Integer_grpd
      walking_circle_direct_encode_function
      p
      (walking_power (walking_encode_function p))
      (@eq_sym
        (Hom WalkingEnd_cat walking_base walking_base)
        (walking_power (walking_encode_function p))
        p
        (@walking_power_encode_roundtrip p)))
    (@walking_to_circle_power_encode (walking_encode_function p));

// The comparison commutes as equality of the two whole carrier functions.
symbol walking_circle_encode_square
  : τ (@=
      (@Function_grpd
        (Hom WalkingEnd_cat walking_base walking_base)
        Integer_grpd)
      walking_circle_direct_encode_function
      walking_circle_via_nat_function)
≔ @PiFunext
    (Hom WalkingEnd_cat walking_base walking_base)
    (λ _ : τ (Hom WalkingEnd_cat walking_base walking_base),
      Integer_grpd)
    walking_circle_direct_encode_function
    walking_circle_via_nat_function
    walking_circle_encode_square_point;
