/*
  Reviewer milestone: the walking-endomorphism directed HIT.

  WalkingEnd is presented independently from its Nat model.  Its dependent
  eliminator consumes a structured Catd motive; point beta is judgmental and
  generator beta is equality evidence.  Generic strict functoriality remains
  the only runtime owner for composite action.  Free-arrow and Nat induction
  then prove the Hom-to-Nat comparison rather than installing it as a rewrite.
*/

require open emdash.emdash3_2_walking_end_hit;
require open emdash.emdash3_2_eq1_hom_action;

// The HIT is the free one-object category on a native directed word generator.
assert ⊢ Obj WalkingEnd_cat ≡ Unit_grpd;

assert ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat WalkingWord_grpd;

assertnot ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat Nat_grpd;

assert ⊢ walking_loop ≡ walking_word_succ walking_word_zero;

// The separate model relates open semantic composition to addition by proof,
// while retaining the composition head as its runtime normal form.
assert (g f : τ Nat_grpd) ⊢
  @bnat_comp_nat_add g f
  : τ (@= Nat_grpd
      (@comp_fapp0 BNat_cat tt tt tt g f)
      (@nat_add g f));

assertnot (g f : τ Nat_grpd) ⊢
  @comp_fapp0 BNat_cat tt tt tt g f
  ≡ @nat_add g f;

// The primitive dependent eliminator has the expected structured interface.
assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @walking_end_ind_sec D u ell
  : τ (Obj (Pi_cat D));

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @walking_end_ind_beta_loop D u ell
  : τ (@=
      (@walking_end_loop_lift_grpd D u)
      (@piapp1_fapp0
        WalkingEnd_cat D (@walking_end_ind_sec D u ell)
        walking_base walking_base walking_loop)
      ell);

// Constant motives expose judgmental point beta and propositional loop beta.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @fapp0 WalkingEnd_cat C (@walking_end_rec_func C x f) walking_base
  ≡ x;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_loop C x f
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f);

assertnot [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @fapp1_fapp0
    WalkingEnd_cat C (@walking_end_rec_func C x f)
    walking_base walking_base walking_loop
  ≡ f;

// The old loop-square conflict is now a theorem using only loop beta and the
// generic Kosta-Došen strict cut.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_loop_square C x f
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x x x f f)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base
        (@comp_fapp0
          WalkingEnd_cat
          walking_base walking_base walking_base
          walking_loop walking_loop)));

// Encoding is derived from the HIT recursor and agrees with word length.
assert (w : τ WalkingWord_grpd) ⊢
  @walking_encode_agreement w
  : τ (@= Nat_grpd
      (@walking_encode_action w)
      (@walking_word_to_nat w));

assert (g f : τ WalkingWord_grpd) ⊢
  @walking_encode_comp_view g f
  : τ (@= Nat_grpd
      (@walking_encode_action
        (@comp_fapp0 WalkingEnd_cat tt tt tt g f))
      (@nat_add (@walking_encode_action g) (@walking_encode_action f)));

// The reverse structured functor agrees with transparent Nat recursion.
assert (n : τ Nat_grpd) ⊢
  @walking_decode_agreement n
  : τ (@= WalkingWord_grpd
      (@walking_decode_action n)
      (@nat_to_walking_word n));

assert (g f : τ Nat_grpd) ⊢
  @walking_decode_comp_view g f
  : τ (@= WalkingWord_grpd
      (@walking_decode_action (@nat_add g f))
      (@comp_fapp0 WalkingEnd_cat tt tt tt
        (@walking_decode_action g)
        (@walking_decode_action f)));

// Both arbitrary inverse laws have transparent induction proofs.
assert (w : τ WalkingWord_grpd) ⊢
  @nat_word_roundtrip w
  : τ (@= WalkingWord_grpd
      (@nat_to_walking_word (@walking_word_to_nat w))
      w);

assert (n : τ Nat_grpd) ⊢
  @word_nat_roundtrip n
  : τ (@= Nat_grpd
      (@walking_word_to_nat (@nat_to_walking_word n))
      n);

assert ⊢ walking_hom_nat_type_equiv
  : τ (TypeEquiv
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd);

assert ⊢
  @omega_equiv_to_EQ1
    Grpd_cat
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_omega_equiv_EQ1
  ≡ walking_word_to_nat;

// Local discreteness does not make the directed generator invertible.
assert ⊢ walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd_cat);

assert ⊢ walking_loop_not_omega_equiv_EQ1
  : τ (@Function_grpd
      (@OmegaEquivAlong_EQ1
        WalkingEnd_cat walking_base walking_base walking_loop)
      Empty_grpd);

assert
  (g : τ (@IsGroupoidalCat_EQ1 WalkingEnd_cat)) ⊢
  @walking_loop_not_omega_equiv_EQ1
    (@groupoidal_arrow_equiv_along_EQ1
      WalkingEnd_cat g walking_base walking_base walking_loop)
  : τ Empty_grpd;
