/*
  Opaque one-dimensional walking-endomorphism directed HIT and separate Nat
  free-monoid consistency model.

  WalkingEnd exposes only its category, base, directed loop, explicit
  one-dimensional evidence, and the contextual Functord eliminator.  Its
  object classifier, hom-categories, identities, and composition stay opaque.
  In particular, BNat is semantic consistency evidence and never the
  definitional Hom of WalkingEnd.

  The contextual base and loop betas are the constructor-specific runtime
  owners. Narrow terminal/constant projection-order joins expose those same
  base and loop betas at the ordinary recursor observers required by concrete
  Code. All other section and recursion observations are transparent theorems
  over those owners and the generic projection calculus.
*/

require open emdash.emdash3_2_nat_arithmetic;

// Opaque HIT formation and introductions.
constant symbol WalkingEnd_cat : Cat;

constant symbol walking_base
  : τ (Obj WalkingEnd_cat);

constant symbol walking_loop
  : τ (Hom WalkingEnd_cat walking_base walking_base);

// Selected one-dimensional truncation evidence; this is signature data.
constant symbol walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd_cat);

// Transparent homwise specializations of the global dimension witness.
symbol walking_end_hom_discrete
  (x y : τ (Obj WalkingEnd_cat))
  : τ (IsDiscreteCat (Hom_cat WalkingEnd_cat x y))
≔ walking_end_is_one_cat x y;

symbol walking_end_based_hom_discrete
  (x : τ (Obj WalkingEnd_cat))
  : τ (IsDiscreteCat
      (Hom_cat WalkingEnd_cat walking_base x))
≔ walking_end_hom_discrete walking_base x;

// A based directed 2-cell becomes equality only through dimension evidence.
symbol walking_end_based_cell_to_path
  (x : τ (Obj WalkingEnd_cat))
  [p q : τ (Hom WalkingEnd_cat walking_base x)]
  (alpha : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base x)
      p q))
  : τ (@=
      (Hom WalkingEnd_cat walking_base x)
      p q)
≔ @hom_to_path
    (Hom_cat WalkingEnd_cat walking_base x)
    (walking_end_based_hom_discrete x)
    p q alpha;

// The opaque category and its explicit dimension evidence as an NCat object.
symbol walking_end_one_cat
  : τ OneCat
≔ @Struct_ncat
    (cat_succ cat_zero)
    WalkingEnd_cat
    walking_end_is_one_cat;

// D[loop] o u.
symbol walking_end_loop_lhs_func
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base))
≔ @comp_cat_fapp0
    (Fibre_cat R walking_base)
    (Fibre_cat D walking_base)
    (Fibre_cat D walking_base)
    (@catd_transport_func
      WalkingEnd_cat D walking_base walking_base walking_loop)
    u;

// u o R[loop].
symbol walking_end_loop_rhs_func
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base))
≔ @comp_cat_fapp0
    (Fibre_cat R walking_base)
    (Fibre_cat R walking_base)
    (Fibre_cat D walking_base)
    u
    (@catd_transport_func
      WalkingEnd_cat R walking_base walking_base walking_loop);

// Contextual loop coherence D[loop] o u => u o R[loop].
symbol walking_end_loop_coherence
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  : Grpd
≔ @Transf
    (Fibre_cat R walking_base)
    (Fibre_cat D walking_base)
    (@walking_end_loop_lhs_func R D u)
    (@walking_end_loop_rhs_func R D u);

// Contextual whole-HIT eliminator indᵈ(R,D,u,sigma) : Functord(R,D).
injective symbol walking_end_ind_funcd
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u))
  : τ (Functord R D);

// Runtime base-constructor beta at the generic fibre-functor projection.
rule @tapp0_fapp0
      WalkingEnd_cat Cat_cat
      $R $D walking_base
      (@walking_end_ind_funcd $R $D $u _)
  ↪ $u;

/*
  Narrow terminal/constant projection-order join. The generic terminal
  component projects the contextual base functor to Obj_func(rec[base]); this
  concrete Code consumer restores the same constructor beta at the ordinary
  fapp0 observer. It is not a second semantic recursor or functoriality owner.
*/
rule @fapp0
      WalkingEnd_cat $C
      (@walking_end_ind_funcd
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat $C)
        (@Const_func Terminal_cat $C $x)
        _)
      walking_base
  ↪ $x;

// Runtime loop-constructor beta at the generic displayed laxity component.
rule @fdapp1_int_cell
      WalkingEnd_cat
      $R $D
      (@walking_end_ind_funcd $R $D $u $sigma)
      walking_base walking_base walking_loop $r
  ↪ @tapp0_fapp0
      (Fibre_cat $R walking_base)
      (Fibre_cat $D walking_base)
      (@walking_end_loop_lhs_func $R $D $u)
      (@walking_end_loop_rhs_func $R $D $u)
      $r $sigma;

// Transparent typed views of the two generic runtime constructor betas.
symbol walking_end_ind_funcd_beta_base
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u))
  : τ (@=
      (Functor
        (Fibre_cat R walking_base)
        (Fibre_cat D walking_base))
      (@Fibre_func
        WalkingEnd_cat R D
        (@walking_end_ind_funcd R D u sigma)
        walking_base)
      u)
≔ @eq_refl
    (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base))
    u;

symbol walking_end_ind_funcd_beta_loop
  (R D : τ (Catd WalkingEnd_cat))
  (u : τ (Functor
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)))
  (sigma : τ (@walking_end_loop_coherence R D u))
  (r : τ (Obj (Fibre_cat R walking_base)))
  : τ (@=
      (Hom
        (Fibre_cat D walking_base)
        (@fapp0
          (Fibre_cat R walking_base)
          (Fibre_cat D walking_base)
          (@walking_end_loop_lhs_func R D u)
          r)
        (@fapp0
          (Fibre_cat R walking_base)
          (Fibre_cat D walking_base)
          (@walking_end_loop_rhs_func R D u)
          r))
      (@fdapp1_int_cell
        WalkingEnd_cat R D
        (@walking_end_ind_funcd R D u sigma)
        walking_base walking_base walking_loop r)
      (@tapp0_fapp0
        (Fibre_cat R walking_base)
        (Fibre_cat D walking_base)
        (@walking_end_loop_lhs_func R D u)
        (@walking_end_loop_rhs_func R D u)
        r sigma))
≔ @eq_refl
    (Hom
      (Fibre_cat D walking_base)
      (@fapp0
        (Fibre_cat R walking_base)
        (Fibre_cat D walking_base)
        (@walking_end_loop_lhs_func R D u)
        r)
      (@fapp0
        (Fibre_cat R walking_base)
        (Fibre_cat D walking_base)
        (@walking_end_loop_rhs_func R D u)
        r))
    (@tapp0_fapp0
      (Fibre_cat R walking_base)
      (Fibre_cat D walking_base)
      (@walking_end_loop_lhs_func R D u)
      (@walking_end_loop_rhs_func R D u)
      r sigma);

// Section-algebra classifier D[loop](u) -> u.
symbol walking_end_loop_lift_grpd
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  : Grpd
≔ Hom
    (Fibre_cat D walking_base)
    (@fapp0
      (Fibre_cat D walking_base)
      (Fibre_cat D walking_base)
      (@catd_transport_func
        WalkingEnd_cat D walking_base walking_base walking_loop)
      u)
    u;

// The section algebra arrow as the unique constant transfor on Terminal.
symbol walking_end_loop_lift_transf
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u))
  : τ (@walking_end_loop_coherence
      (@Const_catd WalkingEnd_cat Terminal_cat)
      D
      (@Obj_func (Fibre_cat D walking_base) u))
≔ @Const_transf
    Terminal_cat
    (Fibre_cat D walking_base)
    (@fapp0
      (Fibre_cat D walking_base)
      (Fibre_cat D walking_base)
      (@catd_transport_func
        WalkingEnd_cat D walking_base walking_base walking_loop)
      u)
    u
    ell;

/*
  Ordinary loop projection of the constant-motive specialization. This is the
  loop-constructor beta exposed at the ordinary fapp1 observer; it does not
  restate generic functoriality away from the literal HIT constructor.
*/
rule @fapp1_fapp0
      WalkingEnd_cat $C
      (@walking_end_ind_funcd
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat $C)
        (@Const_func Terminal_cat $C $x)
        (@Const_transf Terminal_cat $C $x $x $f))
      walking_base walking_base walking_loop
  ↪ $f;

// Derived ordinary section eliminator (R = const(Terminal)).
symbol walking_end_ind_sec
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u))
  : τ (Obj (Pi_cat D))
≔ @walking_end_ind_funcd
    (@Const_catd WalkingEnd_cat Terminal_cat)
    D
    (@Obj_func (Fibre_cat D walking_base) u)
    (@walking_end_loop_lift_transf D u ell);

// Transparent theorem for the derived section's runtime base observation.
symbol walking_end_ind_sec_beta_base
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u))
  : τ (@=
      (Obj (Fibre_cat D walking_base))
      (@piapp0 WalkingEnd_cat D
        (@walking_end_ind_sec D u ell)
        walking_base)
      u)
≔ @eq_refl (Obj (Fibre_cat D walking_base)) u;

// Transparent theorem for the derived section's runtime loop observation.
symbol walking_end_ind_sec_beta_loop
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u))
  : τ (@=
      (@walking_end_loop_lift_grpd D u)
      (@piapp1_fapp0
        WalkingEnd_cat D (@walking_end_ind_sec D u ell)
        walking_base walking_base walking_loop)
      ell)
≔ @eq_refl (@walking_end_loop_lift_grpd D u) ell;

// Derived nondependent recursor (also D = const(C)).
symbol walking_end_rec_func
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (Functor WalkingEnd_cat C)
≔ @walking_end_ind_sec
    (@Const_catd WalkingEnd_cat C)
    x f;

/*
  The terminal/constant specialization has two documented fibre-functor
  reducts. These typed reflexivity theorems retain both generic projection
  views; the narrow ordinary-observer join above selects their common base
  value for the concrete recursor consumer.
*/
symbol walking_end_rec_base_contextual_func_eq
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Functor Terminal_cat C)
      (@Fibre_func
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base)
      (@Obj_func C x))
≔ @walking_end_ind_funcd_beta_base
    (@Const_catd WalkingEnd_cat Terminal_cat)
    (@Const_catd WalkingEnd_cat C)
    (@Obj_func C x)
    (@walking_end_loop_lift_transf
      (@Const_catd WalkingEnd_cat C)
      x f);

symbol walking_end_rec_base_projection_func_eq
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Functor Terminal_cat C)
      (@Fibre_func
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base)
      (@Obj_func C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base)))
≔ @eq_refl
    (Functor Terminal_cat C)
    (@Obj_func C
      (@fapp0 WalkingEnd_cat C
        (@walking_end_rec_func C x f)
        walking_base));

symbol walking_end_rec_base_func_eq
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Functor Terminal_cat C)
      (@Obj_func C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base))
      (@Obj_func C x))
≔ @eq_trans
    (Functor Terminal_cat C)
    (@Obj_func C
      (@fapp0 WalkingEnd_cat C
        (@walking_end_rec_func C x f)
        walking_base))
    (@Fibre_func
      WalkingEnd_cat
      (@Const_catd WalkingEnd_cat Terminal_cat)
      (@Const_catd WalkingEnd_cat C)
      (@walking_end_rec_func C x f)
      walking_base)
    (@Obj_func C x)
    (@eq_sym
      (Functor Terminal_cat C)
      (@Fibre_func
        WalkingEnd_cat
        (@Const_catd WalkingEnd_cat Terminal_cat)
        (@Const_catd WalkingEnd_cat C)
        (@walking_end_rec_func C x f)
        walking_base)
      (@Obj_func C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base))
      (@walking_end_rec_base_projection_func_eq C x f))
    (@walking_end_rec_base_contextual_func_eq C x f);

// Transparent recursor base theorem derived by evaluating that functor path.
symbol walking_end_rec_beta_base
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Obj C)
      (@fapp0 WalkingEnd_cat C
        (@walking_end_rec_func C x f)
        walking_base)
      x)
≔ @eq_ap
      (Functor Terminal_cat C)
      (Obj C)
      (λ F : τ (Functor Terminal_cat C),
        @fapp0 Terminal_cat C F Terminal_obj)
      (@Obj_func C
        (@fapp0 WalkingEnd_cat C
          (@walking_end_rec_func C x f)
          walking_base))
      (@Obj_func C x)
      (@walking_end_rec_base_func_eq C x f);

// Runtime loop theorem at the canonical derived-section observer.
symbol walking_end_rec_beta_loop
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
≔ @walking_end_ind_sec_beta_loop
    (@Const_catd WalkingEnd_cat C)
    x f;

// Proof-time comparison from the section observer to ordinary functor action.
symbol walking_end_rec_loop_ordinary_comparison
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
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
        walking_base walking_base walking_loop))
≔ @piapp1_const_fapp0_eq
    WalkingEnd_cat C
    (@walking_end_rec_func C x f)
    walking_base walking_base walking_loop;

// Typed view of the ordinary runtime loop-constructor beta.
symbol walking_end_rec_beta_loop_ordinary
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f)
≔ @eq_refl (Hom C x x) f;

// --------------------------------------------------------------------------
// Separate Nat free-monoid model: consistency evidence, not definitional Hom.
// --------------------------------------------------------------------------

injective symbol BNat_cat : Cat;
rule Obj BNat_cat ↪ Unit_grpd;
rule Hom_cat BNat_cat _ _ ↪ Path_cat Nat_grpd;
rule @id BNat_cat _ ↪ zero;

rule @comp_fapp0 BNat_cat _ _ _ zero $f ↪ $f
with @comp_fapp0 BNat_cat _ _ _ $g zero ↪ $g
with @comp_fapp0 BNat_cat _ _ _ (succ $g) $f
  ↪ succ (@comp_fapp0 BNat_cat tt tt tt $g $f);

// Proof-time recovery of generic functor-on-identity after id normalizes.
unif_rule
  @fapp1_fapp0 BNat_cat $C $F tt tt zero
  ≡ @id $C (@fapp0 BNat_cat $C $F tt)
  ↪ [ tt ≡ tt ];

symbol bnat_obj : τ (Obj BNat_cat) ≔ tt;

symbol bnat_generator : τ (Hom BNat_cat bnat_obj bnat_obj)
≔ succ zero;

// Open BNat composition agrees propositionally with Nat addition.
symbol bnat_comp_nat_add
  (g f : τ Nat_grpd)
  : τ (@= Nat_grpd
      (@comp_fapp0 BNat_cat tt tt tt g f)
      (@nat_add g f))
≔ @nat_elim
    (λ g : τ Nat_grpd,
      @= Nat_grpd
        (@comp_fapp0 BNat_cat tt tt tt g f)
        (@nat_add g f))
    (@eq_refl Nat_grpd f)
    (λ g0 : τ Nat_grpd,
      λ ih : τ (@= Nat_grpd
        (@comp_fapp0 BNat_cat tt tt tt g0 f)
        (@nat_add g0 f)),
      ih)
    g;

// Path(Nat) is discrete because Nat is a set.
symbol nat_path_discrete
  : τ (IsDiscreteCat (Path_cat Nat_grpd))
≔ @discrete_cat_intro
    (Path_cat Nat_grpd)
    nat_is_set
    (@omega_equiv_along_EQ1_to_D0
      Cat_cat
      (Core_cat (Path_cat Nat_grpd))
      (Path_cat Nat_grpd)
      (Core_incl_func (Path_cat Nat_grpd))
      (@path_cat_is_groupoidal_EQ1 Nat_grpd));

// The separate free-monoid model satisfies the same dimension contract.
symbol bnat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) BNat_cat)
≔ λ _ : τ Unit_grpd,
    λ _ : τ Unit_grpd,
      nat_path_discrete;

symbol bnat_one_cat
  : τ OneCat
≔ @Struct_ncat
    (cat_succ cat_zero)
    BNat_cat
    bnat_is_one_cat;

// Recursor interpretation of the opaque constructors in the separate model.
symbol walking_bnat_model_func
  : τ (Functor WalkingEnd_cat BNat_cat)
≔ @walking_end_rec_func BNat_cat bnat_obj bnat_generator;

symbol walking_bnat_model_beta_base
  : τ (@=
      (Obj BNat_cat)
      (@fapp0
        WalkingEnd_cat BNat_cat walking_bnat_model_func walking_base)
      bnat_obj)
≔ @walking_end_rec_beta_base
    BNat_cat bnat_obj bnat_generator;

// Inferred result preserves the canonical section-observer loop classifier.
symbol walking_bnat_model_beta_loop
≔ @walking_end_rec_beta_loop
    BNat_cat bnat_obj bnat_generator;

// --------------------------------------------------------------------------
// Concrete Code, directed representable, powers, and the contextual spiral.
// --------------------------------------------------------------------------

// Code : WalkingEnd -> Cat, with base Path(Nat) and loop NatSucc.
symbol walking_Code_catd
  : τ (Catd WalkingEnd_cat)
≔ @walking_end_rec_func
    Cat_cat
    (Path_cat Nat_grpd)
    NatSucc_func;

// The narrow recursor projection join makes the Code base runtime-visible.
symbol walking_Code_beta_base
  : τ (@=
      (Obj Cat_cat)
      (Fibre_cat walking_Code_catd walking_base)
      (Path_cat Nat_grpd))
≔ @walking_end_rec_beta_base
    Cat_cat
    (Path_cat Nat_grpd)
    NatSucc_func;

// Typed view of the runtime Code-loop beta.
symbol walking_Code_beta_loop
  : τ (@=
      (Hom Cat_cat (Path_cat Nat_grpd) (Path_cat Nat_grpd))
      (@catd_transport_func
        WalkingEnd_cat walking_Code_catd
        walking_base walking_base walking_loop)
      NatSucc_func)
≔ @walking_end_rec_beta_loop_ordinary
    Cat_cat
    (Path_cat Nat_grpd)
    NatSucc_func;

// encode_x(p) = Code[p](zero).
symbol walking_encode
  [x : τ (Obj WalkingEnd_cat)]
  (p : τ (Hom WalkingEnd_cat walking_base x))
  : τ (Obj (Fibre_cat walking_Code_catd x))
≔ @fapp0
    (Fibre_cat walking_Code_catd walking_base)
    (Fibre_cat walking_Code_catd x)
    (@catd_transport_func
      WalkingEnd_cat walking_Code_catd
      walking_base x p)
    zero;

// Transparent alias for the generic directed based representable.
symbol walking_based_rep_catd
  : τ (Catd WalkingEnd_cat)
≔ @Rep_catd WalkingEnd_cat walking_base;

// Open representable transport is postcomposition in the selected variance.
symbol walking_based_rep_postcomp_eq
  (x : τ (Obj WalkingEnd_cat))
  (p : τ (Hom WalkingEnd_cat walking_base x))
  (q : τ (Hom WalkingEnd_cat walking_base walking_base))
  : τ (@=
      (Hom WalkingEnd_cat walking_base x)
      (@fapp0
        (Fibre_cat walking_based_rep_catd walking_base)
        (Fibre_cat walking_based_rep_catd x)
        (@catd_transport_func
          WalkingEnd_cat walking_based_rep_catd
          walking_base x p)
        q)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base x p q))
≔ @eq_refl
    (Hom WalkingEnd_cat walking_base x)
    (@comp_fapp0
      WalkingEnd_cat walking_base walking_base x p q);

// Postcomposition by loop, inherited from representable transport.
symbol walking_loop_postcomp_func
  : τ (Functor
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (Hom_cat WalkingEnd_cat walking_base walking_base))
≔ @catd_transport_func
    WalkingEnd_cat walking_based_rep_catd
    walking_base walking_base walking_loop;

// power(0)=id and power(succ n)=loop o power(n).
symbol walking_power
  (n : τ Nat_grpd)
  : τ (Hom WalkingEnd_cat walking_base walking_base)
≔ @nat_elim
    (λ _ : τ Nat_grpd,
      Obj (Hom_cat WalkingEnd_cat walking_base walking_base))
    (@id WalkingEnd_cat walking_base)
    (λ _ : τ Nat_grpd,
      λ h : τ (Hom WalkingEnd_cat walking_base walking_base),
      @comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop h)
    n;

symbol walking_power_function
  : τ (@Function_grpd
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base))
≔ λ n : τ Nat_grpd, walking_power n;

// Postcomposition-by-loop after power.
symbol walking_power_left_function
  : τ (@Function_grpd
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base))
≔ @comp_fapp0
    Grpd_cat
    Nat_grpd
    (Hom WalkingEnd_cat walking_base walking_base)
    (Hom WalkingEnd_cat walking_base walking_base)
    (@functor_object_function
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      walking_loop_postcomp_func)
    walking_power_function;

// Power after Nat successor.
symbol walking_power_right_function
  : τ (@Function_grpd
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base))
≔ @comp_fapp0
    Grpd_cat
    Nat_grpd Nat_grpd
    (Hom WalkingEnd_cat walking_base walking_base)
    walking_power_function
    nat_succ_function;

// The pointwise power equation is reflexivity at the raw-composition form.
symbol walking_power_step_point_path
  (n : τ Nat_grpd)
  : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      (@fapp0
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        walking_loop_postcomp_func
        (walking_power n))
      (walking_power (succ n)))
≔ @eq_refl
    (Hom WalkingEnd_cat walking_base walking_base)
    (@comp_fapp0
      WalkingEnd_cat walking_base walking_base walking_base
      walking_loop (walking_power n));

// Pointwise recursion gives equality of the two step functions.
symbol walking_power_step_path
  : τ (@=
      (@Function_grpd
        Nat_grpd
        (Hom WalkingEnd_cat walking_base walking_base))
      walking_power_left_function
      walking_power_right_function)
≔ @PiFunext
    Nat_grpd
    (λ _ : τ Nat_grpd,
      Hom WalkingEnd_cat walking_base walking_base)
    walking_power_left_function
    walking_power_right_function
    (λ n : τ Nat_grpd, @walking_power_step_point_path n);

// Equality action plus Core inclusion lifts power to the directed hom-category.
symbol walking_power_func
  : τ (Functor
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base))
≔ @fapp0
    (Path_cat (@Function_grpd
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base)))
    (Functor_cat
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base))
    (@path_lift_func
      Nat_grpd
      (Hom_cat WalkingEnd_cat walking_base walking_base))
    walking_power_function;

// Canonical directed spiral against the literal Nat successor functor.
symbol walking_power_spiral_natsucc
  : τ (Transf
      (@comp_cat_fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        walking_loop_postcomp_func
        walking_power_func)
      (@comp_cat_fapp0
        (Path_cat Nat_grpd)
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        walking_power_func
        NatSucc_func))
≔ @fapp1_fapp0
    (Path_cat (@Function_grpd
      Nat_grpd
      (Hom WalkingEnd_cat walking_base walking_base)))
    (Functor_cat
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base))
    (@path_lift_func
      Nat_grpd
      (Hom_cat WalkingEnd_cat walking_base walking_base))
    walking_power_left_function
    walking_power_right_function
    walking_power_step_path;

// Code[loop] computes to NatSucc, so the canonical spiral already has the
// literal contextual endpoint; no propositional endpoint whisker is needed.
symbol walking_power_spiral
  : τ (@walking_end_loop_coherence
      walking_Code_catd
      walking_based_rep_catd
      walking_power_func)
≔ walking_power_spiral_natsucc;

// Canonical component before public endpoint adjustments.
symbol walking_power_spiral_component
  (n : τ Nat_grpd)
≔ @tapp0_fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@walking_end_loop_lhs_func
      walking_Code_catd walking_based_rep_catd walking_power_func)
    (@walking_end_loop_rhs_func
      walking_Code_catd walking_based_rep_catd walking_power_func)
    n
    walking_power_spiral;

// Proof-time stable-postcomposition comparison at the spiral source.
symbol walking_power_spiral_source_path
  (n : τ Nat_grpd)
  : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@walking_end_loop_lhs_func
          walking_Code_catd walking_based_rep_catd walking_power_func)
        n)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n)))
≔ @eq_refl
    (Hom WalkingEnd_cat walking_base walking_base)
    (@comp_fapp0
      WalkingEnd_cat walking_base walking_base walking_base
      walking_loop (walking_power n));

// The runtime Code-loop beta evaluated at n as a typed equality witness.
symbol walking_Code_loop_point_path
  (n : τ Nat_grpd)
  : τ (@= Nat_grpd
      (@fapp0
        (Path_cat Nat_grpd)
        (Path_cat Nat_grpd)
        (@catd_transport_func
          WalkingEnd_cat walking_Code_catd
          walking_base walking_base walking_loop)
        n)
      (succ n))
≔ @eq_ap
    (Hom Cat_cat (Path_cat Nat_grpd) (Path_cat Nat_grpd))
    Nat_grpd
    (λ F : τ (Functor (Path_cat Nat_grpd) (Path_cat Nat_grpd)),
      @fapp0 (Path_cat Nat_grpd) (Path_cat Nat_grpd) F n)
    (@catd_transport_func
      WalkingEnd_cat walking_Code_catd
      walking_base walking_base walking_loop)
    NatSucc_func
    walking_Code_beta_loop;

// Directed endpoint adjustments for the readable raw-composition component.
symbol walking_power_spiral_source_adjust
  (n : τ Nat_grpd)
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n))
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@walking_end_loop_lhs_func
          walking_Code_catd walking_based_rep_catd walking_power_func)
        n))
≔ @path_to_hom
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@comp_fapp0
      WalkingEnd_cat walking_base walking_base walking_base
      walking_loop (walking_power n))
    (@fapp0
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@walking_end_loop_lhs_func
        walking_Code_catd walking_based_rep_catd walking_power_func)
      n)
    (@eq_sym
      (Hom WalkingEnd_cat walking_base walking_base)
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@walking_end_loop_lhs_func
          walking_Code_catd walking_based_rep_catd walking_power_func)
        n)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n))
      (@walking_power_spiral_source_path n));

symbol walking_power_spiral_target_adjust
  (n : τ Nat_grpd)
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@walking_end_loop_rhs_func
          walking_Code_catd walking_based_rep_catd walking_power_func)
        n)
      (walking_power (succ n)))
≔ @fapp1_fapp0
    (Path_cat Nat_grpd)
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    walking_power_func
    (@fapp0
      (Path_cat Nat_grpd)
      (Path_cat Nat_grpd)
      (@catd_transport_func
        WalkingEnd_cat walking_Code_catd
        walking_base walking_base walking_loop)
      n)
    (succ n)
    (@walking_Code_loop_point_path n);

// Readable directed component: loop o power(n) -> power(succ n).
symbol walking_power_spiral_cell
  (n : τ Nat_grpd)
  : τ (Hom
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n))
      (walking_power (succ n)))
≔ @comp_fapp0
    (Hom_cat WalkingEnd_cat walking_base walking_base)
    (@comp_fapp0
      WalkingEnd_cat walking_base walking_base walking_base
      walking_loop (walking_power n))
    (@fapp0
      (Path_cat Nat_grpd)
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@walking_end_loop_rhs_func
        walking_Code_catd walking_based_rep_catd walking_power_func)
      n)
    (walking_power (succ n))
    (@walking_power_spiral_target_adjust n)
    (@comp_fapp0
      (Hom_cat WalkingEnd_cat walking_base walking_base)
      (@comp_fapp0
        WalkingEnd_cat walking_base walking_base walking_base
        walking_loop (walking_power n))
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@walking_end_loop_lhs_func
          walking_Code_catd walking_based_rep_catd walking_power_func)
        n)
      (@fapp0
        (Path_cat Nat_grpd)
        (Hom_cat WalkingEnd_cat walking_base walking_base)
        (@walking_end_loop_rhs_func
          walking_Code_catd walking_based_rep_catd walking_power_func)
        n)
      (@walking_power_spiral_component n)
      (@walking_power_spiral_source_adjust n));
