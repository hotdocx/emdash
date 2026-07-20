/*
  Reviewer milestone: the opaque one-dimensional walking-endomorphism HIT.

  WalkingEnd exposes an opaque category, base, directed loop, explicit homwise
  one-dimensional evidence, and a contextual Functord eliminator. No generated
  word carrier or Nat category is definitionally installed as its Hom. BNat is
  retained only as a separate free-monoid consistency model.
*/

require open emdash.emdash3_2_walking_end_hit;

// The selected HIT signature is homwise one-dimensional without exposing its
// object classifier, based hom, identity, or composition.
assert ⊢ walking_base
  : τ (Obj WalkingEnd_cat);

assert ⊢ walking_loop
  : τ (Hom WalkingEnd_cat walking_base walking_base);

assert ⊢ walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd_cat);

assertnot ⊢ Obj WalkingEnd_cat ≡ Unit_grpd;

assertnot ⊢
  Hom_cat WalkingEnd_cat walking_base walking_base
  ≡ Path_cat Nat_grpd;

assertnot ⊢
  @id WalkingEnd_cat walking_base
  ≡ walking_loop;

assertnot ⊢
  @comp_fapp0
    WalkingEnd_cat walking_base walking_base walking_base
    walking_loop walking_loop
  ≡ walking_loop;

// The contextual algebra is D[loop] o u => u o R[loop], and both constructor
// observations compute at the existing generic displayed owners.
assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u)) ⊢
  @walking_end_ind_funcd R D u sigma
  : τ (Functord R D);

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u)) ⊢
  @Fibre_func
      WalkingEnd_cat R D
      (@walking_end_ind_funcd R D u sigma)
      walking_base
  ≡ u;

assert
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u))
  (r : τ (Obj (Fibre_cat R walking_base))) ⊢
  @fdapp1_int_cell
      WalkingEnd_cat R D
      (@walking_end_ind_funcd R D u sigma)
      walking_base walking_base walking_loop r
  ≡ @tapp0_fapp0
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)
      (@walking_end_loop_lhs_func R D u)
      (@walking_end_loop_rhs_func R D u)
      r sigma;

// Ordinary sections are the transparent terminal-source specialization.
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
  @piapp0 WalkingEnd_cat D (@walking_end_ind_sec D u ell) walking_base
  ≡ u;

assert
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u)) ⊢
  @piapp1_fapp0
    WalkingEnd_cat D (@walking_end_ind_sec D u ell)
    walking_base walking_base walking_loop
  ≡ ell;

// The nondependent recursor is also derived. Its ordinary base and loop
// observers satisfy the usual HIT constructor equations by runtime reduction.
assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_func C x f
  : τ (Functor WalkingEnd_cat C);

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @fapp0 WalkingEnd_cat C (@walking_end_rec_func C x f) walking_base
  ≡ x;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @fapp1_fapp0
    WalkingEnd_cat C (@walking_end_rec_func C x f)
    walking_base walking_base walking_loop
  ≡ f;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_base C x f
  : τ (@=
      (Obj C)
      (@fapp0 WalkingEnd_cat C
        (@walking_end_rec_func C x f)
        walking_base)
      x);

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_loop C x f
  ≡ @walking_end_ind_sec_beta_loop
      (@Const_catd WalkingEnd_cat C)
      x f;

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_beta_loop_ordinary C x f
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f);

assert [C : Cat]
  (x : τ (Obj C))
  (f : τ (Hom C x x)) ⊢
  @walking_end_rec_loop_ordinary_comparison C x f
  : τ (@=
      (Hom C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base)
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base))
      (@piapp1_fapp0
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop));

// BNat satisfies the one-object Nat-monoid and dimension contracts separately.
assert ⊢ Obj BNat_cat ≡ Unit_grpd;

assert ⊢
  Hom_cat BNat_cat bnat_obj bnat_obj
  ≡ Path_cat Nat_grpd;

assert (g f : τ Nat_grpd) ⊢
  @bnat_comp_nat_add g f
  : τ (@= Nat_grpd
      (@comp_fapp0 BNat_cat tt tt tt g f)
      (@nat_add g f));

assertnot (g f : τ Nat_grpd) ⊢
  @comp_fapp0 BNat_cat tt tt tt g f
  ≡ @nat_add g f;

assert ⊢ bnat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) BNat_cat);

assert ⊢ walking_bnat_model_func
  : τ (Functor WalkingEnd_cat BNat_cat);

assert ⊢ walking_bnat_model_beta_base
  : τ (@=
      (Obj BNat_cat)
      (@fapp0
        WalkingEnd_cat BNat_cat walking_bnat_model_func walking_base)
      bnat_obj);

assert ⊢ walking_bnat_model_beta_loop
  ≡ @walking_end_rec_beta_loop
      BNat_cat bnat_obj bnat_generator;

// Code is the concrete Cat-valued recursor. Both constructor equations are
// directly computational, including the loop action used by the spiral.
assert ⊢
  Fibre_cat walking_Code_catd walking_base
  ≡ Path_cat Nat_grpd;

assert ⊢
  @catd_transport_func
    WalkingEnd_cat walking_Code_catd
    walking_base walking_base walking_loop
  ≡ NatSucc_func;

assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_encode x p
  : τ (Obj (Fibre_cat walking_Code_catd x));

// Nat powers are lifted to a functor from Path(Nat) into the directed based
// endomorphism category.
assert ⊢
  walking_power zero
  ≡ @id WalkingEnd_cat walking_base;

assert (n : τ Nat_grpd) ⊢
  walking_power (succ n)
  ≡ @comp_fapp0
      WalkingEnd_cat walking_base walking_base walking_base
      walking_loop (walking_power n);

assert (n : τ Nat_grpd) ⊢
  @fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    walking_power_func n
  ≡ walking_power n;

// The contextual algebra is a directed spiral. Its readable component has
// the literal endpoint loop o power(n) -> power(succ n).
assert ⊢ walking_power_spiral
  : τ (@walking_end_loop_coherence
      walking_Code_catd
      walking_based_rep_catd
      walking_power_func);

// The equality-local CoreInclTransf redesign constructs the selected contextual
// algebra as PathLift(step) o kappa-left. The right comparison is judgmentally
// identity, so it is deliberately absent rather than inserted as a third cell.
assert ⊢ walking_power_spiral_coreincl
  : τ (@walking_end_loop_coherence
      walking_Code_catd
      walking_based_rep_catd
      walking_power_func);

assert ⊢
  walking_power_spiral_coreincl
  ≡ walking_power_spiral;

assert (n : τ Nat_grpd) ⊢
  @walking_power_spiral_cell n
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n))
      (walking_power (succ n)));

// The underlying point equality computes to reflexivity. The final directed
// cell retains generic representable endpoint transports, so it is not
// misleadingly claimed to be the raw categorical identity by conversion.
assert (n : τ Nat_grpd) ⊢
  @PiHapply
    Nat_grpd
    (λ _ : τ Nat_grpd,
      Hom WalkingEnd_cat walking_base walking_base)
    walking_power_left_function
    walking_power_right_function
    walking_power_step_path
    n
  ≡ @eq_refl
      (Hom WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n));

assertnot (n : τ Nat_grpd) ⊢
  @walking_power_spiral_cell n
  ≡ @id
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n));

// The contextual decoder is constructed from Code, the directed
// representable, power, and the spiral—there is no eliminator on an exposed
// Hom carrier.
assert ⊢ walking_directed_decode_funcd
  : τ (Functord walking_Code_catd walking_based_rep_catd);

assert ⊢
  @walking_directed_decode_func walking_base
  ≡ walking_power_func;

// At an arbitrary opaque p, the displayed action at zero is already the
// directed normalization cell p -> decode_x(encode_x(p)).
assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_directed_normalization_cell x p
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base x)
      p
      (@walking_directed_decode x (@walking_encode x p)));

assert
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x)) ⊢
  @walking_directed_normalization_cell x p
  ≡ @fdapp1_int_cell
      WalkingEnd_cat
      walking_Code_catd
      walking_based_rep_catd
      walking_directed_decode_funcd
      walking_base x p zero;

// One-dimensionality upgrades that directed cell to equality; at the base it
// gives the hard inverse.
assert
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_power_encode_roundtrip p
  : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      (walking_power (@walking_encode walking_base p))
      p);

// The composite Code action is a named proof-time equation, not a third HIT
// runtime rule. Native Nat induction then supplies the easy inverse.
assert (n : τ Nat_grpd) ⊢
  @walking_encode_power_succ_path n
  : τ (@= Nat_grpd
      (@walking_encode walking_base (walking_power (succ n)))
      (succ (@walking_encode walking_base (walking_power n))));

assertnot (n : τ Nat_grpd) ⊢
  @walking_encode walking_base (walking_power (succ n))
  ≡ succ (@walking_encode walking_base (walking_power n));

assert (n : τ Nat_grpd) ⊢
  @walking_encode_power_roundtrip n
  : τ (@= Nat_grpd
      (@walking_encode walking_base (walking_power n))
      n);

// The two semantic inverses now package the actual opaque Hom carrier as Nat;
// BNat remains a separate model rather than a definitional presentation.
assert ⊢ walking_encode_func
  : τ (Functor
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (Path_cat Nat_grpd));

assert ⊢ walking_hom_nat_type_equiv
  : τ (TypeEquiv
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd);

assert ⊢
  @type_equiv_to
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_type_equiv
  ≡ walking_encode_function;

assert ⊢
  @type_equiv_from
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_type_equiv
  ≡ walking_power_function;

// One-dimensional signature data and the carrier equivalence independently
// establish Hom sethood; neither is confused with the other.
assert ⊢ walking_end_hom_is_set_from_dimension
  : τ (IsSetGrpd
      (Hom WalkingEnd_cat walking_base walking_base));

assert ⊢ walking_end_hom_is_set_from_equiv
  : τ (IsSetGrpd
      (Hom WalkingEnd_cat walking_base walking_base));

// Encoding sends loop prefixes to successors, so the directed loop is neither
// identity nor invertible.
assert
  (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @walking_encode_loop_prefix_path p
  : τ (@= Nat_grpd
      (@walking_encode walking_base
        (@comp_fapp0
          WalkingEnd_cat walking_base walking_base walking_base
          walking_loop p))
      (succ (@walking_encode walking_base p)));

assert
  (u : τ (@OmegaEquivAlong_EQ1
      WalkingEnd_cat walking_base walking_base walking_loop)) ⊢
  @walking_loop_not_omega_equiv_EQ1 u
  : τ Empty_grpd;
