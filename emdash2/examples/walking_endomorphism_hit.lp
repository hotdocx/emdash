/*
  Reviewer milestone: the walking-endomorphism directed HIT.

  WalkingEnd is presented independently from its Nat model.  Its dependent
  eliminator consumes a structured Catd motive; point beta is judgmental and
  generator beta is equality evidence.  Generic strict functoriality remains
  the only runtime owner for composite action.  The HIT's intrinsic hom
  induction and Nat induction prove inverse laws for the actual semantic
  encode/decode actions rather than for a parallel pair of helper functions.
*/

require open emdash.emdash3_2_walking_end_hit;
require open emdash.emdash3_2_eq1_hom_action;

// The native generated-hom carrier is the intrinsic arrow part of the HIT,
// while BNat below is the separate normal-form model.
assert ⊢ Obj WalkingEnd_cat ≡ Unit_grpd;

assert ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat WalkingEndHom_grpd;

assertnot ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat Nat_grpd;

assert ⊢ walking_loop ≡ walking_end_hom_step walking_end_hom_id;

assert
  (P : τ WalkingEndHom_grpd → Grpd)
  (z : τ (P walking_end_hom_id))
  (s : Π w : τ WalkingEndHom_grpd,
    τ (P w) → τ (P (walking_end_hom_step w)))
  (w : τ WalkingEndHom_grpd) ⊢
  @walking_end_hom_ind P z s (walking_end_hom_step w)
  ≡ s w (@walking_end_hom_ind P z s w);

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

// Practical recursor computation is generic in the target, not BNat-specific.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  (w : τ WalkingEndHom_grpd) ⊢
  @walking_end_rec_step_view C x f w
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base (walking_end_hom_step w))
      (@comp_fapp0
        C x x x f
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base w)));

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

// Encoding is derived from the HIT recursor; its successor theorem consumes
// the primitive loop beta and generic strict functoriality.
assert (w : τ WalkingEndHom_grpd) ⊢
  @walking_encode_succ_view w
  : τ (@= Nat_grpd
      (@walking_encode_action (walking_end_hom_step w))
      (succ (@walking_encode_action w)));

assert (g f : τ WalkingEndHom_grpd) ⊢
  @walking_encode_comp_view g f
  : τ (@= Nat_grpd
      (@walking_encode_action
        (@comp_fapp0 WalkingEnd_cat tt tt tt g f))
      (@nat_add (@walking_encode_action g) (@walking_encode_action f)));

// The reverse structured functor's successor theorem consumes its generator
// beta and generic strict functoriality.
assert (n : τ Nat_grpd) ⊢
  @walking_decode_succ_view n
  : τ (@= WalkingEndHom_grpd
      (@walking_decode_action (succ n))
      (walking_end_hom_step (@walking_decode_action n)));

assert (g f : τ Nat_grpd) ⊢
  @walking_decode_comp_view g f
  : τ (@= WalkingEndHom_grpd
      (@walking_decode_action (@nat_add g f))
      (@comp_fapp0 WalkingEnd_cat tt tt tt
        (@walking_decode_action g)
        (@walking_decode_action f)));

// This is the practical freeness computation: the decisive source-side proof
// is hom-level HIT induction over the actual recursor/decoder actions.
assert (w : τ WalkingEndHom_grpd) ⊢
  @walking_decode_encode_roundtrip w
  : τ (@= WalkingEndHom_grpd
      (@walking_decode_action (@walking_encode_action w))
      w);

assert (n : τ Nat_grpd) ⊢
  @walking_encode_decode_roundtrip n
  : τ (@= Nat_grpd
      (@walking_encode_action (@walking_decode_action n))
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
  ≡ walking_encode_action;

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
