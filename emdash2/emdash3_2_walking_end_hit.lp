/*
  Walking endomorphism directed-HIT and Nat normal-form model.

  The HIT section is an ambient strict functor.  Generic strict
  functoriality therefore remains the sole runtime owner of composite action;
  the displayed loop constructor has a primitive equality beta, following
  the ordinary intensional Circle interface, rather than a competing raw
  action rewrite.  Generated-hom and Nat induction derive both semantic
  encode/decode round trips.

  `walking_end_hom` is not a second model beside the HIT: it is the native
  carrier of `Hom(WalkingEnd,base,base)`, and `walking_end_hom_ind` is the hom
  component of the directed-HIT elimination interface.  `BNat_cat` is the
  separate Nat normal-form model.  The Hom-to-Nat result is packaged from the
  actual semantic functor actions only after their transparent inverse proofs.
*/

require open emdash.emdash3_2_nat_arithmetic;

// Intrinsic generated-hom carrier of the walking directed HIT.
inductive walking_end_hom : TYPE ≔
| walking_end_hom_id : walking_end_hom
| walking_end_hom_step : walking_end_hom → walking_end_hom;

constant symbol WalkingEndHom_grpd : Grpd;
rule τ WalkingEndHom_grpd ↪ walking_end_hom;
rule @= WalkingEndHom_grpd walking_end_hom_id walking_end_hom_id ↪ Unit_grpd
with @= WalkingEndHom_grpd walking_end_hom_id (walking_end_hom_step _) ↪ Empty_grpd
with @= WalkingEndHom_grpd (walking_end_hom_step _) walking_end_hom_id ↪ Empty_grpd
with @= WalkingEndHom_grpd (walking_end_hom_step $m) (walking_end_hom_step $n)
  ↪ @= WalkingEndHom_grpd $m $n;

// Hom-level HIT induction over every generated directed arrow.
symbol walking_end_hom_ind
  (P : τ WalkingEndHom_grpd → Grpd)
  (z : τ (P walking_end_hom_id))
  (s : Π w : τ WalkingEndHom_grpd, τ (P w) → τ (P (walking_end_hom_step w)))
  (w : τ WalkingEndHom_grpd)
  : τ (P w)
≔ ind_walking_end_hom P z s w;

// Free strict one-object category on one directed generator.
injective symbol WalkingEnd_cat : Cat;
rule Obj WalkingEnd_cat ↪ Unit_grpd;
rule Hom_cat WalkingEnd_cat _ _ ↪ Path_cat WalkingEndHom_grpd;
rule @id WalkingEnd_cat _ ↪ walking_end_hom_id;

// Composition consumes the visible outer/left generated arrow.
rule @comp_fapp0 WalkingEnd_cat _ _ _ walking_end_hom_id $f ↪ $f
with @comp_fapp0 WalkingEnd_cat _ _ _ $g walking_end_hom_id ↪ $g
with @comp_fapp0 WalkingEnd_cat _ _ _ (walking_end_hom_step $g) $f
  ↪ walking_end_hom_step (@comp_fapp0 WalkingEnd_cat tt tt tt $g $f);

/*
  Proof-time recovery of generic functor-on-identity after the source identity
  has normalized to the intrinsic hom-identity constructor. Runtime still has
  one owner: the global literal-identity functor rule.
*/
unif_rule
  @fapp1_fapp0 WalkingEnd_cat $C $F tt tt walking_end_hom_id
  ≡ @id $C (@fapp0 WalkingEnd_cat $C $F tt)
  ↪ [ tt ≡ tt ];

symbol walking_functor_id_view
  [C : Cat]
  (F : τ (Functor WalkingEnd_cat C))
  : τ (@=
      (Hom C
        (@fapp0 WalkingEnd_cat C F tt)
        (@fapp0 WalkingEnd_cat C F tt))
      (@fapp1_fapp0 WalkingEnd_cat C F tt tt walking_end_hom_id)
      (@id C (@fapp0 WalkingEnd_cat C F tt)))
≔ @eq_refl
    (Hom C
      (@fapp0 WalkingEnd_cat C F tt)
      (@fapp0 WalkingEnd_cat C F tt))
    (@id C (@fapp0 WalkingEnd_cat C F tt));

symbol walking_base : τ (Obj WalkingEnd_cat) ≔ tt;
symbol walking_loop : τ (Hom WalkingEnd_cat walking_base walking_base)
≔ walking_end_hom_step walking_end_hom_id;

// Displayed generator algebra D[loop](u) -> u.
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

// Primitive directed-HIT eliminator into a structured Catd motive.
injective symbol walking_end_ind_sec
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u))
  : τ (Obj (Pi_cat D));

// Runtime point-constructor beta at terminal section evaluation.
rule @fapp0
      _ _
      (@tapp0_fapp0
        _ Cat_cat
        (@Const_catd WalkingEnd_cat Terminal_cat)
        _
        tt
        (@walking_end_ind_sec _ $u _))
      Terminal_obj
  ↪ $u;

/*
  Generator beta as primitive equality evidence.  It is deliberately not a
  rewrite of the raw section action: generic strict-functor composition keeps
  sole ownership of composite-action runtime normalization.
*/
injective symbol walking_end_ind_beta_loop
  (D : τ (Catd WalkingEnd_cat))
  (u : τ (Obj (Fibre_cat D walking_base)))
  (ell : τ (@walking_end_loop_lift_grpd D u))
  : τ (@=
      (@walking_end_loop_lift_grpd D u)
      (@piapp1_fapp0
        WalkingEnd_cat D (@walking_end_ind_sec D u ell)
        walking_base walking_base walking_loop)
      ell);

// Nondependent recursor is the constant-motive specialization.
symbol walking_end_rec_func
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (Functor WalkingEnd_cat C)
≔ @walking_end_ind_sec (@Const_catd WalkingEnd_cat C) x f;

// Readable object projection routes through the dependent eliminator.
// lhs-audit: keep 1,2 -- source/target select the Pi/Functor comparison.
rule @fapp0
      WalkingEnd_cat $C
      (@walking_end_ind_sec
        (@Const_catd WalkingEnd_cat $C)
        $x _)
      _
  ↪ $x;

// The ordinary recursor's loop beta is the dependent beta specialization.
symbol walking_end_rec_beta_loop
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f)
≔ @walking_end_ind_beta_loop
    (@Const_catd WalkingEnd_cat C)
    x f;

/*
  Generic generated-arrow step computation for every recursor target.

  Strict functoriality first identifies action on `step(w) = loop o w` with
  `F[loop] o F[w]`; whiskering the HIT loop beta then replaces `F[loop]` by
  the supplied generator image.  No target-specific action rule is needed.
*/
symbol walking_end_rec_step_view
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  (w : τ WalkingEndHom_grpd)
  : τ (@=
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base (walking_end_hom_step w))
      (@comp_fapp0
        C x x x f
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base w)))
≔ @eq_trans
    (Hom C x x)
    (@fapp1_fapp0
      WalkingEnd_cat C (@walking_end_rec_func C x f)
      walking_base walking_base (walking_end_hom_step w))
    (@comp_fapp0
      C x x x
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base w))
    (@comp_fapp0
      C x x x f
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base w))
    (@eq_refl
      (Hom C x x)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base (walking_end_hom_step w)))
    (@eq_ap
      (Hom C x x)
      (Hom C x x)
      (λ h : τ (Hom C x x),
        @comp_fapp0
          C x x x h
          (@fapp1_fapp0
            WalkingEnd_cat C (@walking_end_rec_func C x f)
            walking_base walking_base w))
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f
      (@walking_end_rec_beta_loop C x f));

/*
  The former runtime critical pair is now a derived equality.  The final
  reflexivity witness uses only the global Kosta-Došen strict cut:
    F[loop] o F[loop] -> F[loop o loop].
*/
symbol walking_end_rec_loop_square
  (C : Cat)
  (x : τ (Obj C))
  (f : τ (Hom C x x))
  : τ (@=
      (Hom C x x)
      (@comp_fapp0 C x x x f f)
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base
        (@comp_fapp0
          WalkingEnd_cat
          walking_base walking_base walking_base
          walking_loop walking_loop)))
≔ @eq_trans
    (Hom C x x)
    (@comp_fapp0 C x x x f f)
    (@comp_fapp0 C x x x
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      f)
    (@fapp1_fapp0
      WalkingEnd_cat C (@walking_end_rec_func C x f)
      walking_base walking_base
      (@comp_fapp0
        WalkingEnd_cat
        walking_base walking_base walking_base
        walking_loop walking_loop))
    (@eq_ap
      (Hom C x x)
      (Hom C x x)
      (λ h : τ (Hom C x x), @comp_fapp0 C x x x h f)
      f
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base walking_loop)
      (@eq_sym
        (Hom C x x)
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base walking_loop)
        f
        (@walking_end_rec_beta_loop C x f)))
    (@eq_trans
      (Hom C x x)
      (@comp_fapp0 C x x x
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base walking_loop)
        f)
      (@comp_fapp0 C x x x
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base walking_loop)
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base walking_loop))
      (@fapp1_fapp0
        WalkingEnd_cat C (@walking_end_rec_func C x f)
        walking_base walking_base
        (@comp_fapp0
          WalkingEnd_cat
          walking_base walking_base walking_base
          walking_loop walking_loop))
      (@eq_ap
        (Hom C x x)
        (Hom C x x)
        (λ h : τ (Hom C x x),
          @comp_fapp0 C x x x
            (@fapp1_fapp0
              WalkingEnd_cat C (@walking_end_rec_func C x f)
              walking_base walking_base walking_loop)
            h)
        f
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base walking_loop)
        (@eq_sym
          (Hom C x x)
          (@fapp1_fapp0
            WalkingEnd_cat C (@walking_end_rec_func C x f)
            walking_base walking_base walking_loop)
          f
          (@walking_end_rec_beta_loop C x f)))
      (@eq_refl
        (Hom C x x)
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base
          (@comp_fapp0
            WalkingEnd_cat
            walking_base walking_base walking_base
            walking_loop walking_loop))));

// Separate one-object Nat monoid model.
injective symbol BNat_cat : Cat;
rule Obj BNat_cat ↪ Unit_grpd;
rule Hom_cat BNat_cat _ _ ↪ Path_cat Nat_grpd;
rule @id BNat_cat _ ↪ zero;

rule @comp_fapp0 BNat_cat _ _ _ zero $f ↪ $f
with @comp_fapp0 BNat_cat _ _ _ $g zero ↪ $g
with @comp_fapp0 BNat_cat _ _ _ (succ $g) $f
  ↪ succ (@comp_fapp0 BNat_cat tt tt tt $g $f);

/*
  Proof-time recovery of generic functor-on-identity after the BNat identity
  has normalized to zero. Runtime remains owned by the literal-identity rule.
*/
unif_rule
  @fapp1_fapp0 BNat_cat $C $F tt tt zero
  ≡ @id $C (@fapp0 BNat_cat $C $F tt)
  ↪ [ tt ≡ tt ];

symbol bnat_functor_zero_view
  [C : Cat]
  (F : τ (Functor BNat_cat C))
  : τ (@=
      (Hom C
        (@fapp0 BNat_cat C F tt)
        (@fapp0 BNat_cat C F tt))
      (@fapp1_fapp0 BNat_cat C F tt tt zero)
      (@id C (@fapp0 BNat_cat C F tt)))
≔ @eq_refl
    (Hom C
      (@fapp0 BNat_cat C F tt)
      (@fapp0 BNat_cat C F tt))
    (@id C (@fapp0 BNat_cat C F tt));

symbol bnat_obj : τ (Obj BNat_cat) ≔ tt;
symbol bnat_generator : τ (Hom BNat_cat bnat_obj bnat_obj)
≔ succ zero;

// Open BNat composition agrees propositionally with selected Nat addition.
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

// The HIT recursor supplies the structured encoding functor.
symbol walking_encode_func : τ (Functor WalkingEnd_cat BNat_cat)
≔ @walking_end_rec_func BNat_cat bnat_obj bnat_generator;

// Its capped hom action remains a named semantic projection.
symbol walking_encode_action
  (w : τ WalkingEndHom_grpd)
  : τ Nat_grpd
≔ @fapp1_fapp0
    WalkingEnd_cat BNat_cat walking_encode_func
    walking_base walking_base w;

symbol walking_encode_id_view
  : τ (@= Nat_grpd (@walking_encode_action walking_end_hom_id) zero)
≔ @walking_functor_id_view BNat_cat walking_encode_func;

// The encoder successor law is the generic recursor step theorem at BNat.
symbol walking_encode_succ_view
  (w : τ WalkingEndHom_grpd)
  : τ (@= Nat_grpd
      (@walking_encode_action (walking_end_hom_step w))
      (succ (@walking_encode_action w)))
≔ @walking_end_rec_step_view
    BNat_cat bnat_obj bnat_generator w;

// Strict encoding sends generated-arrow composition to selected Nat addition.
symbol walking_encode_comp_view
  (g f : τ WalkingEndHom_grpd)
  : τ (@= Nat_grpd
      (@walking_encode_action
        (@comp_fapp0 WalkingEnd_cat tt tt tt g f))
      (@nat_add
        (@walking_encode_action g)
        (@walking_encode_action f)))
≔ @eq_trans
    Nat_grpd
    (@walking_encode_action
      (@comp_fapp0 WalkingEnd_cat tt tt tt g f))
    (@comp_fapp0
      BNat_cat tt tt tt
      (@walking_encode_action g)
      (@walking_encode_action f))
    (@nat_add
      (@walking_encode_action g)
      (@walking_encode_action f))
    (@eq_refl
      Nat_grpd
      (@walking_encode_action
        (@comp_fapp0 WalkingEnd_cat tt tt tt g f)))
    (@bnat_comp_nat_add
      (@walking_encode_action g)
      (@walking_encode_action f));

// The intrinsic hom classifier is set-valued by nested hom induction.
symbol walking_end_hom_is_set
  : τ (IsSetGrpd WalkingEndHom_grpd)
≔ λ m : τ WalkingEndHom_grpd,
    @walking_end_hom_ind
      (λ m : τ WalkingEndHom_grpd,
        @Pi_grpd WalkingEndHom_grpd
          (λ n : τ WalkingEndHom_grpd,
            IsPropGrpd (@= WalkingEndHom_grpd m n)))
      (λ n : τ WalkingEndHom_grpd,
        @walking_end_hom_ind
          (λ n : τ WalkingEndHom_grpd,
            IsPropGrpd (@= WalkingEndHom_grpd walking_end_hom_id n))
          unit_is_prop
          (λ n0 : τ WalkingEndHom_grpd,
            λ _ : τ (IsPropGrpd (@= WalkingEndHom_grpd walking_end_hom_id n0)),
            empty_is_prop)
          n)
      (λ m0 : τ WalkingEndHom_grpd,
        λ ih : τ (@Pi_grpd WalkingEndHom_grpd
          (λ n : τ WalkingEndHom_grpd,
            IsPropGrpd (@= WalkingEndHom_grpd m0 n))),
        λ n : τ WalkingEndHom_grpd,
          @walking_end_hom_ind
            (λ n : τ WalkingEndHom_grpd,
              IsPropGrpd (@= WalkingEndHom_grpd (walking_end_hom_step m0) n))
            empty_is_prop
            (λ n0 : τ WalkingEndHom_grpd,
              λ _ : τ (IsPropGrpd
                (@= WalkingEndHom_grpd (walking_end_hom_step m0) n0)),
              ih n0)
            n)
      m;

// Literal path categories over sets satisfy the active discrete contract.
symbol walking_end_hom_path_discrete
  : τ (IsDiscreteCat (Path_cat WalkingEndHom_grpd))
≔ @discrete_cat_intro
    (Path_cat WalkingEndHom_grpd)
    walking_end_hom_is_set
    (@omega_equiv_along_EQ1_to_D0
      Cat_cat
      (Core_cat (Path_cat WalkingEndHom_grpd))
      (Path_cat WalkingEndHom_grpd)
      (Core_incl_func (Path_cat WalkingEndHom_grpd))
      (@path_cat_is_groupoidal_EQ1 WalkingEndHom_grpd));

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

// Both one-object categories are internally one-dimensional.
symbol walking_end_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) WalkingEnd_cat)
≔ λ _ : τ Unit_grpd,
    λ _ : τ Unit_grpd,
      walking_end_hom_path_discrete;

symbol bnat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) BNat_cat)
≔ λ _ : τ Unit_grpd,
    λ _ : τ Unit_grpd,
      nat_path_discrete;

symbol walking_end_one_cat
  : τ OneCat
≔ @Struct_ncat
    (cat_succ cat_zero)
    WalkingEnd_cat
    walking_end_is_one_cat;

symbol bnat_one_cat
  : τ OneCat
≔ @Struct_ncat
    (cat_succ cat_zero)
    BNat_cat
    bnat_is_one_cat;

// The generator is not the identity, and no left inverse can exist.
symbol walking_loop_not_identity
  (p : τ (@= WalkingEndHom_grpd walking_loop walking_end_hom_id))
  : τ Empty_grpd
≔ p;

symbol walking_loop_no_left_inverse
  (w : τ WalkingEndHom_grpd)
  : τ (@Function_grpd
      (@= WalkingEndHom_grpd
        (@comp_fapp0 WalkingEnd_cat tt tt tt w walking_loop)
        walking_end_hom_id)
      Empty_grpd)
≔ @walking_end_hom_ind
    (λ w : τ WalkingEndHom_grpd,
      @Function_grpd
        (@= WalkingEndHom_grpd
          (@comp_fapp0 WalkingEnd_cat tt tt tt w walking_loop)
          walking_end_hom_id)
        Empty_grpd)
    (λ p : τ Empty_grpd, p)
    (λ w0 : τ WalkingEndHom_grpd,
      λ _ : τ (@Function_grpd
        (@= WalkingEndHom_grpd
          (@comp_fapp0 WalkingEnd_cat tt tt tt w0 walking_loop)
          walking_end_hom_id)
        Empty_grpd),
      λ p : τ Empty_grpd, p)
    w;

// In particular, the directed loop cannot carry omega-equivalence evidence.
symbol walking_loop_not_omega_equiv_EQ1
  (u : τ (@OmegaEquivAlong_EQ1
      WalkingEnd_cat walking_base walking_base walking_loop))
  : τ Empty_grpd
≔ (@walking_loop_no_left_inverse
      (@omega_equiv_along_left_inv_EQ1
        WalkingEnd_cat walking_base walking_base walking_loop u))
    (@omega_equiv_along_left_law_EQ1
      WalkingEnd_cat walking_base walking_base walking_loop u);

/*
  Structured reverse comparison.

  Emdash functors are semantic objects rather than records assembled from raw
  carrier functions.  This stable functor head is therefore the selected
  BNat-to-WalkingEnd map; its generator beta is equality evidence, and the
  complete capped action is derived below by Nat induction.
*/
injective symbol walking_decode_func
  : τ (Functor BNat_cat WalkingEnd_cat);

rule @fapp0
      BNat_cat WalkingEnd_cat walking_decode_func _
  ↪ walking_base;

injective symbol walking_decode_beta_generator
  : τ (@=
      (Hom WalkingEnd_cat walking_base walking_base)
      (@fapp1_fapp0
        BNat_cat WalkingEnd_cat walking_decode_func
        bnat_obj bnat_obj bnat_generator)
      walking_loop);

symbol walking_decode_action
  (n : τ Nat_grpd)
  : τ WalkingEndHom_grpd
≔ @fapp1_fapp0
    BNat_cat WalkingEnd_cat walking_decode_func
    bnat_obj bnat_obj n;

symbol walking_decode_zero_view
  : τ (@= WalkingEndHom_grpd (@walking_decode_action zero) walking_end_hom_id)
≔ @bnat_functor_zero_view WalkingEnd_cat walking_decode_func;

// Strictness plus the generator beta derives the successor action law.
symbol walking_decode_succ_view
  (n : τ Nat_grpd)
  : τ (@= WalkingEndHom_grpd
      (@walking_decode_action (succ n))
      (walking_end_hom_step (@walking_decode_action n)))
≔ @eq_trans
    WalkingEndHom_grpd
    (@walking_decode_action (succ n))
    (@comp_fapp0
      WalkingEnd_cat tt tt tt
      (@walking_decode_action bnat_generator)
      (@walking_decode_action n))
    (walking_end_hom_step (@walking_decode_action n))
    (@eq_refl WalkingEndHom_grpd (@walking_decode_action (succ n)))
    (@eq_ap
      (Hom WalkingEnd_cat walking_base walking_base)
      (Hom WalkingEnd_cat walking_base walking_base)
      (λ h : τ (Hom WalkingEnd_cat walking_base walking_base),
        @comp_fapp0
          WalkingEnd_cat tt tt tt h (@walking_decode_action n))
      (@walking_decode_action bnat_generator)
      walking_loop
      walking_decode_beta_generator);

// Strict decoding sends selected Nat addition to generated-arrow composition.
symbol walking_decode_comp_view
  (g f : τ Nat_grpd)
  : τ (@= WalkingEndHom_grpd
      (@walking_decode_action (@nat_add g f))
      (@comp_fapp0
        WalkingEnd_cat tt tt tt
        (@walking_decode_action g)
        (@walking_decode_action f)))
≔ @eq_trans
    WalkingEndHom_grpd
    (@walking_decode_action (@nat_add g f))
    (@walking_decode_action
      (@comp_fapp0 BNat_cat tt tt tt g f))
    (@comp_fapp0
      WalkingEnd_cat tt tt tt
      (@walking_decode_action g)
      (@walking_decode_action f))
    (@eq_ap
      Nat_grpd WalkingEndHom_grpd
      walking_decode_action
      (@nat_add g f)
      (@comp_fapp0 BNat_cat tt tt tt g f)
      (@eq_sym
        Nat_grpd
        (@comp_fapp0 BNat_cat tt tt tt g f)
        (@nat_add g f)
        (@bnat_comp_nat_add g f)))
    (@eq_refl
      WalkingEndHom_grpd
      (@walking_decode_action
        (@comp_fapp0 BNat_cat tt tt tt g f)));

/*
  Practical HIT computation on arbitrary arrows.

  The forward map is the actual action of the recursor-derived encoder; its
  successor law uses the primitive HIT loop beta.  The inverse is the actual
  action of the structured decoder; its successor law uses the decoder's
  generator beta.  Hom-level HIT induction and Nat induction extend those
  constructor laws to the two open semantic round trips.
*/
symbol walking_decode_encode_roundtrip
  (w : τ WalkingEndHom_grpd)
  : τ (@= WalkingEndHom_grpd
      (@walking_decode_action (@walking_encode_action w))
      w)
≔ @walking_end_hom_ind
    (λ w : τ WalkingEndHom_grpd,
      @= WalkingEndHom_grpd
        (@walking_decode_action (@walking_encode_action w))
        w)
    (@eq_trans
      WalkingEndHom_grpd
      (@walking_decode_action (@walking_encode_action walking_end_hom_id))
      (@walking_decode_action zero)
      walking_end_hom_id
      (@eq_ap
        Nat_grpd WalkingEndHom_grpd
        walking_decode_action
        (@walking_encode_action walking_end_hom_id)
        zero
        walking_encode_id_view)
      walking_decode_zero_view)
    (λ w0 : τ WalkingEndHom_grpd,
      λ ih : τ (@= WalkingEndHom_grpd
        (@walking_decode_action (@walking_encode_action w0))
        w0),
      @eq_trans
        WalkingEndHom_grpd
        (@walking_decode_action
          (@walking_encode_action (walking_end_hom_step w0)))
        (walking_end_hom_step
          (@walking_decode_action (@walking_encode_action w0)))
        (walking_end_hom_step w0)
        (@eq_trans
          WalkingEndHom_grpd
          (@walking_decode_action
            (@walking_encode_action (walking_end_hom_step w0)))
          (@walking_decode_action (succ (@walking_encode_action w0)))
          (walking_end_hom_step
            (@walking_decode_action (@walking_encode_action w0)))
          (@eq_ap
            Nat_grpd WalkingEndHom_grpd
            walking_decode_action
            (@walking_encode_action (walking_end_hom_step w0))
            (succ (@walking_encode_action w0))
            (@walking_encode_succ_view w0))
          (@walking_decode_succ_view (@walking_encode_action w0)))
        (@eq_ap
          WalkingEndHom_grpd WalkingEndHom_grpd
          (λ w1 : τ WalkingEndHom_grpd, walking_end_hom_step w1)
          (@walking_decode_action (@walking_encode_action w0))
          w0
          ih))
    w;

symbol walking_encode_decode_roundtrip
  (n : τ Nat_grpd)
  : τ (@= Nat_grpd
      (@walking_encode_action (@walking_decode_action n))
      n)
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @= Nat_grpd
        (@walking_encode_action (@walking_decode_action n))
        n)
    (@eq_trans
      Nat_grpd
      (@walking_encode_action (@walking_decode_action zero))
      (@walking_encode_action walking_end_hom_id)
      zero
      (@eq_ap
        WalkingEndHom_grpd Nat_grpd
        walking_encode_action
        (@walking_decode_action zero)
        walking_end_hom_id
        walking_decode_zero_view)
      walking_encode_id_view)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@= Nat_grpd
        (@walking_encode_action (@walking_decode_action n0))
        n0),
      @eq_trans
        Nat_grpd
        (@walking_encode_action (@walking_decode_action (succ n0)))
        (succ (@walking_encode_action (@walking_decode_action n0)))
        (succ n0)
        (@eq_trans
          Nat_grpd
          (@walking_encode_action (@walking_decode_action (succ n0)))
          (@walking_encode_action
            (walking_end_hom_step (@walking_decode_action n0)))
          (succ (@walking_encode_action (@walking_decode_action n0)))
          (@eq_ap
            WalkingEndHom_grpd Nat_grpd
            walking_encode_action
            (@walking_decode_action (succ n0))
            (walking_end_hom_step (@walking_decode_action n0))
            (@walking_decode_succ_view n0))
          (@walking_encode_succ_view (@walking_decode_action n0)))
        (@eq_ap
          Nat_grpd Nat_grpd
          (λ n1 : τ Nat_grpd, succ n1)
          (@walking_encode_action (@walking_decode_action n0))
          n0
          ih))
    n;

// Package the semantic hom equivalence through the active interfaces.
symbol walking_hom_nat_by_inverse
  : τ (@EquivByInverse
      WalkingEndHom_grpd Nat_grpd
      walking_encode_action walking_decode_action)
≔ @Struct_sigma
    (@Pi_grpd WalkingEndHom_grpd
      (λ w : τ WalkingEndHom_grpd,
        @= WalkingEndHom_grpd
          (@walking_decode_action (@walking_encode_action w))
          w))
    (λ _ : τ (@Pi_grpd WalkingEndHom_grpd
      (λ w : τ WalkingEndHom_grpd,
        @= WalkingEndHom_grpd
          (@walking_decode_action (@walking_encode_action w))
          w)),
      @Pi_grpd Nat_grpd
        (λ n : τ Nat_grpd,
          @= Nat_grpd
            (@walking_encode_action (@walking_decode_action n))
            n))
    walking_decode_encode_roundtrip
    walking_encode_decode_roundtrip;

symbol walking_hom_nat_type_equiv
  : τ (TypeEquiv
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd)
≔ @Struct_sigma
    (@Function_grpd WalkingEndHom_grpd Nat_grpd)
    (λ map : τ (@Function_grpd WalkingEndHom_grpd Nat_grpd),
      @IsEquivMap WalkingEndHom_grpd Nat_grpd map)
    walking_encode_action
    (@is_equiv_map_by_inverse
      WalkingEndHom_grpd Nat_grpd
      walking_encode_action walking_decode_action
      walking_hom_nat_by_inverse);

symbol walking_hom_nat_omega_equiv_EQ1
  : τ (@OmegaEquiv_EQ1
      Grpd_cat
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd)
≔ @type_equiv_to_omega_EQ1
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_type_equiv;
