/*
  Walking endomorphism directed-HIT and Nat normal-form model.

  The HIT section is an ambient strict functor.  Generic strict
  functoriality therefore remains the sole runtime owner of composite action;
  the displayed loop constructor has a primitive equality beta, following
  the ordinary intensional Circle interface, rather than a competing raw
  action rewrite.  Free-arrow and Nat induction derive the complete capped
  encode/decode actions and both round trips.

  WalkingWord is intentionally distinct from Nat.  The Hom-to-Nat result is
  packaged only after transparent inverse proofs, and the directed loop is
  proved nonidentity and noninvertible rather than declared groupoidal.
*/

require open emdash.emdash3_2;

/*
  Natural-number addition.

  The primary recursion is on the left argument.  The open right-unit fold is
  an intentional second equation: it joins the two ordinary category-unit
  orders in future one-object monoid presentations.  The two reduction paths
  at `nat_add (succ m) zero` meet at `succ m`.
*/
injective symbol nat_add
  (m n : τ Nat_grpd)
  : τ Nat_grpd;

rule @nat_add zero $n ↪ $n
with @nat_add (succ $m) $n ↪ succ (@nat_add $m $n)
with @nat_add $m zero ↪ $m;

// Associativity of the selected addition orientation, by Nat induction.
symbol nat_add_assoc
  (m n k : τ Nat_grpd)
  : τ (@= Nat_grpd
      (@nat_add (@nat_add m n) k)
      (@nat_add m (@nat_add n k)))
≔ @nat_elim
    (λ m : τ Nat_grpd,
      @= Nat_grpd
        (@nat_add (@nat_add m n) k)
        (@nat_add m (@nat_add n k)))
    (@eq_refl Nat_grpd (@nat_add n k))
    (λ m0 : τ Nat_grpd,
      λ ih : τ (@= Nat_grpd
        (@nat_add (@nat_add m0 n) k)
        (@nat_add m0 (@nat_add n k))),
      ih)
    m;

// Unit is contractible, using its generated dependent eliminator.
symbol unit_is_contr
  : τ (IsContr Unit_grpd)
≔ @Struct_sigma
    Unit_grpd
    (λ centre : τ Unit_grpd,
      @Pi_grpd Unit_grpd
        (λ x : τ Unit_grpd, @= Unit_grpd centre x))
    tt
    (λ x : τ Unit_grpd,
      @ind_unit
        (λ x : τ Unit_grpd, @= Unit_grpd tt x)
        (@eq_refl Unit_grpd tt)
        x);

// Unit is proposition-valued by general contractibility monotonicity.
symbol unit_is_prop
  : τ (IsPropGrpd Unit_grpd)
≔ @is_contr_is_prop Unit_grpd unit_is_contr;

// Empty is proposition-valued by elimination at its first endpoint.
symbol empty_is_prop
  : τ (IsPropGrpd Empty_grpd)
≔ λ x : τ Empty_grpd,
    @empty_elim
      (λ _ : τ Empty_grpd,
        @Pi_grpd Empty_grpd
          (λ y : τ Empty_grpd,
            IsContr (@= Empty_grpd x y)))
      x;

/*
  Nat is set-valued.

  Nested Nat induction reduces every visible equality classifier to Unit or
  Empty and reuses the proposition-valuedness proofs above.  This is an
  internal inhabitant of `IsSetGrpd Nat_grpd`, not a conclusion inferred only
  from constructor no-confusion rewrites.
*/
symbol nat_is_set
  : τ (IsSetGrpd Nat_grpd)
≔ λ m : τ Nat_grpd,
    @nat_elim
      (λ m : τ Nat_grpd,
        @Pi_grpd Nat_grpd
          (λ n : τ Nat_grpd,
            IsPropGrpd (@= Nat_grpd m n)))
      (λ n : τ Nat_grpd,
        @nat_elim
          (λ n : τ Nat_grpd,
            IsPropGrpd (@= Nat_grpd zero n))
          unit_is_prop
          (λ n0 : τ Nat_grpd,
            λ _ : τ (IsPropGrpd (@= Nat_grpd zero n0)),
            empty_is_prop)
          n)
      (λ m0 : τ Nat_grpd,
        λ ih : τ (@Pi_grpd Nat_grpd
          (λ n : τ Nat_grpd,
            IsPropGrpd (@= Nat_grpd m0 n))),
        λ n : τ Nat_grpd,
          @nat_elim
            (λ n : τ Nat_grpd,
              IsPropGrpd (@= Nat_grpd (succ m0) n))
            empty_is_prop
            (λ n0 : τ Nat_grpd,
              λ _ : τ (IsPropGrpd
                (@= Nat_grpd (succ m0) n0)),
              ih n0)
            n)
      m;

// Native free-arrow syntax, intentionally distinct from Nat.
inductive walking_word : TYPE ≔
| walking_word_zero : walking_word
| walking_word_succ : walking_word → walking_word;

constant symbol WalkingWord_grpd : Grpd;
rule τ WalkingWord_grpd ↪ walking_word;
rule @= WalkingWord_grpd walking_word_zero walking_word_zero ↪ Unit_grpd
with @= WalkingWord_grpd walking_word_zero (walking_word_succ _) ↪ Empty_grpd
with @= WalkingWord_grpd (walking_word_succ _) walking_word_zero ↪ Empty_grpd
with @= WalkingWord_grpd (walking_word_succ $m) (walking_word_succ $n)
  ↪ @= WalkingWord_grpd $m $n;

symbol walking_word_elim
  (P : τ WalkingWord_grpd → Grpd)
  (z : τ (P walking_word_zero))
  (s : Π w : τ WalkingWord_grpd, τ (P w) → τ (P (walking_word_succ w)))
  (w : τ WalkingWord_grpd)
  : τ (P w)
≔ ind_walking_word P z s w;

// Free strict one-object category on one directed generator.
injective symbol WalkingEnd_cat : Cat;
rule Obj WalkingEnd_cat ↪ Unit_grpd;
rule Hom_cat WalkingEnd_cat _ _ ↪ Path_cat WalkingWord_grpd;
rule @id WalkingEnd_cat _ ↪ walking_word_zero;

// Composition consumes the visible outer/left word.
rule @comp_fapp0 WalkingEnd_cat _ _ _ walking_word_zero $f ↪ $f
with @comp_fapp0 WalkingEnd_cat _ _ _ $g walking_word_zero ↪ $g
with @comp_fapp0 WalkingEnd_cat _ _ _ (walking_word_succ $g) $f
  ↪ walking_word_succ (@comp_fapp0 WalkingEnd_cat tt tt tt $g $f);

/*
  Proof-time recovery of generic functor-on-identity after the source identity
  has normalized to the native zero constructor.  Runtime still has one
  owner: the global literal-identity functor rule.
*/
unif_rule
  @fapp1_fapp0 WalkingEnd_cat $C $F tt tt walking_word_zero
  ≡ @id $C (@fapp0 WalkingEnd_cat $C $F tt)
  ↪ [ tt ≡ tt ];

symbol walking_functor_zero_view
  [C : Cat]
  (F : τ (Functor WalkingEnd_cat C))
  : τ (@=
      (Hom C
        (@fapp0 WalkingEnd_cat C F tt)
        (@fapp0 WalkingEnd_cat C F tt))
      (@fapp1_fapp0 WalkingEnd_cat C F tt tt walking_word_zero)
      (@id C (@fapp0 WalkingEnd_cat C F tt)))
≔ @eq_refl
    (Hom C
      (@fapp0 WalkingEnd_cat C F tt)
      (@fapp0 WalkingEnd_cat C F tt))
    (@id C (@fapp0 WalkingEnd_cat C F tt));

symbol walking_base : τ (Obj WalkingEnd_cat) ≔ tt;
symbol walking_loop : τ (Hom WalkingEnd_cat walking_base walking_base)
≔ walking_word_succ walking_word_zero;

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

// Point beta remains judgmental; loop beta is an inhabitable equality.
assert [C : Cat] (x : τ (Obj C)) (f : τ (Hom C x x))
  ⊢ @fapp0 WalkingEnd_cat C (@walking_end_rec_func C x f) walking_base ≡ x;

assert [C : Cat] (x : τ (Obj C)) (f : τ (Hom C x x))
  ⊢ @walking_end_rec_beta_loop C x f
    : τ (@=
        (Hom C x x)
        (@fapp1_fapp0
          WalkingEnd_cat C (@walking_end_rec_func C x f)
          walking_base walking_base walking_loop)
        f);

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

assert [C : Cat] (x : τ (Obj C)) (f : τ (Hom C x x))
  ⊢ @walking_end_rec_loop_square C x f
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
  (w : τ WalkingWord_grpd)
  : τ Nat_grpd
≔ @fapp1_fapp0
    WalkingEnd_cat BNat_cat walking_encode_func
    walking_base walking_base w;

symbol walking_encode_zero_view
  : τ (@= Nat_grpd (@walking_encode_action walking_word_zero) zero)
≔ @walking_functor_zero_view BNat_cat walking_encode_func;

// Transparent free-word length and its inverse word constructor.
symbol walking_word_to_nat
  (w : τ WalkingWord_grpd)
  : τ Nat_grpd
≔ @walking_word_elim
    (λ _ : τ WalkingWord_grpd, Nat_grpd)
    zero
    (λ _ : τ WalkingWord_grpd,
      λ n : τ Nat_grpd, succ n)
    w;

symbol nat_to_walking_word
  (n : τ Nat_grpd)
  : τ WalkingWord_grpd
≔ @nat_elim
    (λ _ : τ Nat_grpd, WalkingWord_grpd)
    walking_word_zero
    (λ _ : τ Nat_grpd,
      λ w : τ WalkingWord_grpd, walking_word_succ w)
    n;

// Word length preserves the selected composition/addition orientation.
symbol walking_word_to_nat_comp
  (g f : τ WalkingWord_grpd)
  : τ (@= Nat_grpd
      (@walking_word_to_nat
        (@comp_fapp0 WalkingEnd_cat tt tt tt g f))
      (@nat_add (@walking_word_to_nat g) (@walking_word_to_nat f)))
≔ @walking_word_elim
    (λ g : τ WalkingWord_grpd,
      @= Nat_grpd
        (@walking_word_to_nat
          (@comp_fapp0 WalkingEnd_cat tt tt tt g f))
        (@nat_add (@walking_word_to_nat g) (@walking_word_to_nat f)))
    (@eq_refl Nat_grpd (@walking_word_to_nat f))
    (λ g0 : τ WalkingWord_grpd,
      λ ih : τ (@= Nat_grpd
        (@walking_word_to_nat
          (@comp_fapp0 WalkingEnd_cat tt tt tt g0 f))
        (@nat_add (@walking_word_to_nat g0) (@walking_word_to_nat f))),
      ih)
    g;

/*
  Derived successor law for the encoding functor.

  The first equality is reflexivity after the global strict cut
    encode[loop] o encode[w] -> encode[loop o w].
  The second whisks the primitive loop-beta equality; BNat composition then
  computes `one o n` to `succ n`.
*/
symbol walking_encode_succ_view
  (w : τ WalkingWord_grpd)
  : τ (@= Nat_grpd
      (@walking_encode_action (walking_word_succ w))
      (succ (@walking_encode_action w)))
≔ @eq_trans
    Nat_grpd
    (@walking_encode_action (walking_word_succ w))
    (@comp_fapp0
      BNat_cat tt tt tt
      (@walking_encode_action walking_loop)
      (@walking_encode_action w))
    (succ (@walking_encode_action w))
    (@eq_refl Nat_grpd (@walking_encode_action (walking_word_succ w)))
    (@eq_ap
      (Hom BNat_cat bnat_obj bnat_obj)
      (Hom BNat_cat bnat_obj bnat_obj)
      (λ h : τ (Hom BNat_cat bnat_obj bnat_obj),
        @comp_fapp0
          BNat_cat tt tt tt h (@walking_encode_action w))
      (@walking_encode_action walking_loop)
      bnat_generator
      (@walking_end_rec_beta_loop
        BNat_cat bnat_obj bnat_generator));

// Strict encoding sends word composition to selected Nat addition.
symbol walking_encode_comp_view
  (g f : τ WalkingWord_grpd)
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

// All recursor actions agree propositionally with transparent word length.
symbol walking_encode_agreement
  (w : τ WalkingWord_grpd)
  : τ (@= Nat_grpd
      (@walking_encode_action w)
      (@walking_word_to_nat w))
≔ @walking_word_elim
    (λ w : τ WalkingWord_grpd,
      @= Nat_grpd
        (@walking_encode_action w)
        (@walking_word_to_nat w))
    walking_encode_zero_view
    (λ w0 : τ WalkingWord_grpd,
      λ ih : τ (@= Nat_grpd
        (@walking_encode_action w0)
        (@walking_word_to_nat w0)),
      @eq_trans
        Nat_grpd
        (@walking_encode_action (walking_word_succ w0))
        (succ (@walking_encode_action w0))
        (succ (@walking_word_to_nat w0))
        (@walking_encode_succ_view w0)
        (@eq_ap
          Nat_grpd Nat_grpd
          (λ n : τ Nat_grpd, succ n)
          (@walking_encode_action w0)
          (@walking_word_to_nat w0)
          ih))
    w;

// Transparent inverse round trips use the directed free-arrow induction.
symbol nat_word_roundtrip
  (w : τ WalkingWord_grpd)
  : τ (@= WalkingWord_grpd
      (@nat_to_walking_word (@walking_word_to_nat w))
      w)
≔ @walking_word_elim
    (λ w : τ WalkingWord_grpd,
      @= WalkingWord_grpd
        (@nat_to_walking_word (@walking_word_to_nat w))
        w)
    (@eq_refl WalkingWord_grpd walking_word_zero)
    (λ w0 : τ WalkingWord_grpd,
      λ ih : τ (@= WalkingWord_grpd
        (@nat_to_walking_word (@walking_word_to_nat w0))
        w0),
      ih)
    w;

symbol word_nat_roundtrip
  (n : τ Nat_grpd)
  : τ (@= Nat_grpd
      (@walking_word_to_nat (@nat_to_walking_word n))
      n)
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @= Nat_grpd
        (@walking_word_to_nat (@nat_to_walking_word n))
        n)
    (@eq_refl Nat_grpd zero)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@= Nat_grpd
        (@walking_word_to_nat (@nat_to_walking_word n0))
        n0),
      ih)
    n;

// The free-word classifier is set-valued by nested constructor induction.
symbol walking_word_is_set
  : τ (IsSetGrpd WalkingWord_grpd)
≔ λ m : τ WalkingWord_grpd,
    @walking_word_elim
      (λ m : τ WalkingWord_grpd,
        @Pi_grpd WalkingWord_grpd
          (λ n : τ WalkingWord_grpd,
            IsPropGrpd (@= WalkingWord_grpd m n)))
      (λ n : τ WalkingWord_grpd,
        @walking_word_elim
          (λ n : τ WalkingWord_grpd,
            IsPropGrpd (@= WalkingWord_grpd walking_word_zero n))
          unit_is_prop
          (λ n0 : τ WalkingWord_grpd,
            λ _ : τ (IsPropGrpd (@= WalkingWord_grpd walking_word_zero n0)),
            empty_is_prop)
          n)
      (λ m0 : τ WalkingWord_grpd,
        λ ih : τ (@Pi_grpd WalkingWord_grpd
          (λ n : τ WalkingWord_grpd,
            IsPropGrpd (@= WalkingWord_grpd m0 n))),
        λ n : τ WalkingWord_grpd,
          @walking_word_elim
            (λ n : τ WalkingWord_grpd,
              IsPropGrpd (@= WalkingWord_grpd (walking_word_succ m0) n))
            empty_is_prop
            (λ n0 : τ WalkingWord_grpd,
              λ _ : τ (IsPropGrpd
                (@= WalkingWord_grpd (walking_word_succ m0) n0)),
              ih n0)
            n)
      m;

// Literal path categories over sets satisfy the active discrete contract.
symbol walking_word_path_discrete
  : τ (IsDiscreteCat (Path_cat WalkingWord_grpd))
≔ @discrete_cat_intro
    (Path_cat WalkingWord_grpd)
    walking_word_is_set
    (@omega_equiv_along_EQ1_to_D0
      Cat_cat
      (Core_cat (Path_cat WalkingWord_grpd))
      (Path_cat WalkingWord_grpd)
      (Core_incl_func (Path_cat WalkingWord_grpd))
      (@path_cat_is_groupoidal_EQ1 WalkingWord_grpd));

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
      walking_word_path_discrete;

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
  (p : τ (@= WalkingWord_grpd walking_loop walking_word_zero))
  : τ Empty_grpd
≔ p;

symbol walking_loop_no_left_inverse
  (w : τ WalkingWord_grpd)
  : τ (@Function_grpd
      (@= WalkingWord_grpd
        (@comp_fapp0 WalkingEnd_cat tt tt tt w walking_loop)
        walking_word_zero)
      Empty_grpd)
≔ @walking_word_elim
    (λ w : τ WalkingWord_grpd,
      @Function_grpd
        (@= WalkingWord_grpd
          (@comp_fapp0 WalkingEnd_cat tt tt tt w walking_loop)
          walking_word_zero)
        Empty_grpd)
    (λ p : τ Empty_grpd, p)
    (λ w0 : τ WalkingWord_grpd,
      λ _ : τ (@Function_grpd
        (@= WalkingWord_grpd
          (@comp_fapp0 WalkingEnd_cat tt tt tt w0 walking_loop)
          walking_word_zero)
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
  : τ WalkingWord_grpd
≔ @fapp1_fapp0
    BNat_cat WalkingEnd_cat walking_decode_func
    bnat_obj bnat_obj n;

symbol walking_decode_zero_view
  : τ (@= WalkingWord_grpd (@walking_decode_action zero) walking_word_zero)
≔ @bnat_functor_zero_view WalkingEnd_cat walking_decode_func;

// Strictness plus the generator beta derives the successor action law.
symbol walking_decode_succ_view
  (n : τ Nat_grpd)
  : τ (@= WalkingWord_grpd
      (@walking_decode_action (succ n))
      (walking_word_succ (@walking_decode_action n)))
≔ @eq_trans
    WalkingWord_grpd
    (@walking_decode_action (succ n))
    (@comp_fapp0
      WalkingEnd_cat tt tt tt
      (@walking_decode_action bnat_generator)
      (@walking_decode_action n))
    (walking_word_succ (@walking_decode_action n))
    (@eq_refl WalkingWord_grpd (@walking_decode_action (succ n)))
    (@eq_ap
      (Hom WalkingEnd_cat walking_base walking_base)
      (Hom WalkingEnd_cat walking_base walking_base)
      (λ h : τ (Hom WalkingEnd_cat walking_base walking_base),
        @comp_fapp0
          WalkingEnd_cat tt tt tt h (@walking_decode_action n))
      (@walking_decode_action bnat_generator)
      walking_loop
      walking_decode_beta_generator);

// The structured decoder agrees with transparent Nat recursion at every n.
symbol walking_decode_agreement
  (n : τ Nat_grpd)
  : τ (@= WalkingWord_grpd
      (@walking_decode_action n)
      (@nat_to_walking_word n))
≔ @nat_elim
    (λ n : τ Nat_grpd,
      @= WalkingWord_grpd
        (@walking_decode_action n)
        (@nat_to_walking_word n))
    walking_decode_zero_view
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@= WalkingWord_grpd
        (@walking_decode_action n0)
        (@nat_to_walking_word n0)),
      @eq_trans
        WalkingWord_grpd
        (@walking_decode_action (succ n0))
        (walking_word_succ (@walking_decode_action n0))
        (walking_word_succ (@nat_to_walking_word n0))
        (@walking_decode_succ_view n0)
        (@eq_ap
          WalkingWord_grpd WalkingWord_grpd
          (λ w : τ WalkingWord_grpd, walking_word_succ w)
          (@walking_decode_action n0)
          (@nat_to_walking_word n0)
          ih))
    n;

// Strict decoding sends selected Nat addition to word composition.
symbol walking_decode_comp_view
  (g f : τ Nat_grpd)
  : τ (@= WalkingWord_grpd
      (@walking_decode_action (@nat_add g f))
      (@comp_fapp0
        WalkingEnd_cat tt tt tt
        (@walking_decode_action g)
        (@walking_decode_action f)))
≔ @eq_trans
    WalkingWord_grpd
    (@walking_decode_action (@nat_add g f))
    (@walking_decode_action
      (@comp_fapp0 BNat_cat tt tt tt g f))
    (@comp_fapp0
      WalkingEnd_cat tt tt tt
      (@walking_decode_action g)
      (@walking_decode_action f))
    (@eq_ap
      Nat_grpd WalkingWord_grpd
      walking_decode_action
      (@nat_add g f)
      (@comp_fapp0 BNat_cat tt tt tt g f)
      (@eq_sym
        Nat_grpd
        (@comp_fapp0 BNat_cat tt tt tt g f)
        (@nat_add g f)
        (@bnat_comp_nat_add g f)))
    (@eq_refl
      WalkingWord_grpd
      (@walking_decode_action
        (@comp_fapp0 BNat_cat tt tt tt g f)));

// Package the transparent hom equivalence through the active interfaces.
symbol walking_word_nat_by_inverse
  : τ (@EquivByInverse
      WalkingWord_grpd Nat_grpd
      walking_word_to_nat nat_to_walking_word)
≔ @Struct_sigma
    (@Pi_grpd WalkingWord_grpd
      (λ w : τ WalkingWord_grpd,
        @= WalkingWord_grpd
          (@nat_to_walking_word (@walking_word_to_nat w))
          w))
    (λ _ : τ (@Pi_grpd WalkingWord_grpd
      (λ w : τ WalkingWord_grpd,
        @= WalkingWord_grpd
          (@nat_to_walking_word (@walking_word_to_nat w))
          w)),
      @Pi_grpd Nat_grpd
        (λ n : τ Nat_grpd,
          @= Nat_grpd
            (@walking_word_to_nat (@nat_to_walking_word n))
            n))
    nat_word_roundtrip
    word_nat_roundtrip;

symbol walking_hom_nat_type_equiv
  : τ (TypeEquiv
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd)
≔ @Struct_sigma
    (@Function_grpd WalkingWord_grpd Nat_grpd)
    (λ map : τ (@Function_grpd WalkingWord_grpd Nat_grpd),
      @IsEquivMap WalkingWord_grpd Nat_grpd map)
    walking_word_to_nat
    (@is_equiv_map_by_inverse
      WalkingWord_grpd Nat_grpd
      walking_word_to_nat nat_to_walking_word
      walking_word_nat_by_inverse);

symbol walking_hom_nat_omega_equiv_EQ1
  : τ (@OmegaEquiv_EQ1
      Grpd_cat
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd)
≔ @type_equiv_to_omega_EQ1
    (Hom WalkingEnd_cat walking_base walking_base)
    Nat_grpd
    walking_hom_nat_type_equiv;

assert (w : τ WalkingWord_grpd)
  ⊢ @walking_encode_agreement w
    : τ (@= Nat_grpd (@walking_encode_action w) (@walking_word_to_nat w));

assert (w : τ WalkingWord_grpd)
  ⊢ @nat_word_roundtrip w
    : τ (@= WalkingWord_grpd
        (@nat_to_walking_word (@walking_word_to_nat w))
        w);

assert (n : τ Nat_grpd)
  ⊢ @word_nat_roundtrip n
    : τ (@= Nat_grpd
        (@walking_word_to_nat (@nat_to_walking_word n))
        n);

assert (n : τ Nat_grpd)
  ⊢ @walking_decode_agreement n
    : τ (@= WalkingWord_grpd
        (@walking_decode_action n)
        (@nat_to_walking_word n));

assert
  ⊢ sigma_Fst walking_hom_nat_type_equiv ≡ walking_word_to_nat;

assert
  ⊢ @omega_equiv_to_EQ1
      Grpd_cat
      (Hom WalkingEnd_cat walking_base walking_base)
      Nat_grpd
      walking_hom_nat_omega_equiv_EQ1
    ≡ walking_word_to_nat;

assertnot (w : τ WalkingWord_grpd)
  ⊢ @nat_to_walking_word (@walking_word_to_nat w) ≡ w;

assertnot (n : τ Nat_grpd)
  ⊢ @walking_word_to_nat (@nat_to_walking_word n) ≡ n;
