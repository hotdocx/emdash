/*
  Structured commutative-ring morphisms and their ordinary category.

  A morphism retains a carrier function and five proposition-valued witnesses;
  the category facade leaves whole arrows at the generic category owners.
  Pointwise equality extends to full structured-map equality without eta. A
  downstream localization-overlap consumer selects one stable pointwise
  composition comparison; a carrier functor remains a later layer.
*/

require open emdash.emdash3_2_commutative_algebra;

symbol CommRingHomPreservesZero
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : Grpd
≔ @= (@comm_ring_carrier S)
    (f (@comm_ring_zero R))
    (@comm_ring_zero S);

symbol CommRingHomPreservesOne
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : Grpd
≔ @= (@comm_ring_carrier S)
    (f (@comm_ring_one R))
    (@comm_ring_one S);

symbol CommRingHomPreservesAdd
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : Grpd
≔ @Pi_grpd
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @Pi_grpd
        (@comm_ring_carrier R)
        (λ y : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier S)
            (f (@comm_ring_add R x y))
            (@comm_ring_add S (f x) (f y))));

symbol CommRingHomPreservesNeg
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : Grpd
≔ @Pi_grpd
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (f (@comm_ring_neg R x))
        (@comm_ring_neg S (f x)));

symbol CommRingHomPreservesMul
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : Grpd
≔ @Pi_grpd
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @Pi_grpd
        (@comm_ring_carrier R)
        (λ y : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier S)
            (f (@comm_ring_mul R x y))
            (@comm_ring_mul S (f x) (f y))));

// Five preservation fields; negation is retained for first-order usability.
symbol CommRingHomLaws
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : Grpd
≔ `Σ_ zero : τ (@CommRingHomPreservesZero R S f),
   `Σ_ one : τ (@CommRingHomPreservesOne R S f),
   `Σ_ add : τ (@CommRingHomPreservesAdd R S f),
   `Σ_ neg : τ (@CommRingHomPreservesNeg R S f),
       @CommRingHomPreservesMul R S f;

symbol comm_ring_hom_laws_intro
  [R S : τ CommRing]
  [f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))]
  (zero : τ (@CommRingHomPreservesZero R S f))
  (one : τ (@CommRingHomPreservesOne R S f))
  (add : τ (@CommRingHomPreservesAdd R S f))
  (neg : τ (@CommRingHomPreservesNeg R S f))
  (mul : τ (@CommRingHomPreservesMul R S f))
  : τ (@CommRingHomLaws R S f)
≔ Struct_sigma zero
    (Struct_sigma one
      (Struct_sigma add
        (Struct_sigma neg mul)));

symbol CommRingHom
  (R S : τ CommRing)
  : Grpd
≔ `Σ_ f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)),
    @CommRingHomLaws R S f;

symbol comm_ring_hom_intro
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  (laws : τ (@CommRingHomLaws R S f))
  : τ (@CommRingHom R S)
≔ @Struct_sigma
    (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))
    (λ g : τ (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)),
      @CommRingHomLaws R S g)
    f laws;

symbol comm_ring_hom_function
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))
≔ sigma_Fst h;

symbol comm_ring_hom_laws
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingHomLaws R S (@comm_ring_hom_function R S h))
≔ sigma_Snd h;

// Readable projections of the five retained preservation witnesses.
symbol comm_ring_hom_zero_law
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingHomPreservesZero
      R S (@comm_ring_hom_function R S h))
≔ sigma_Fst (@comm_ring_hom_laws R S h);

symbol comm_ring_hom_one_law
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingHomPreservesOne
      R S (@comm_ring_hom_function R S h))
≔ sigma_Fst (sigma_Snd (@comm_ring_hom_laws R S h));

symbol comm_ring_hom_add_law
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingHomPreservesAdd
      R S (@comm_ring_hom_function R S h))
≔ sigma_Fst (sigma_Snd (sigma_Snd (@comm_ring_hom_laws R S h)));

symbol comm_ring_hom_neg_law
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingHomPreservesNeg
      R S (@comm_ring_hom_function R S h))
≔ sigma_Fst
    (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_hom_laws R S h))));

symbol comm_ring_hom_mul_law
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  : τ (@CommRingHomPreservesMul
      R S (@comm_ring_hom_function R S h))
≔ sigma_Snd
    (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_hom_laws R S h))));

// Transparent point application; it owns no category-cut computation.
symbol comm_ring_hom_apply
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (x : τ (@comm_ring_carrier R))
  : τ (@comm_ring_carrier S)
≔ @comm_ring_hom_function R S h x;

// Each preservation classifier is a property because the target is a set.
symbol comm_ring_hom_preserves_zero_is_prop
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingHomPreservesZero R S f))
≔ (@comm_ring_carrier_is_set S)
    (f (@comm_ring_zero R))
    (@comm_ring_zero S);

symbol comm_ring_hom_preserves_one_is_prop
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingHomPreservesOne R S f))
≔ (@comm_ring_carrier_is_set S)
    (f (@comm_ring_one R))
    (@comm_ring_one S);

symbol comm_ring_hom_preserves_add_is_prop
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingHomPreservesAdd R S f))
≔ @is_prop_pi
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @Pi_grpd
        (@comm_ring_carrier R)
        (λ y : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier S)
            (f (@comm_ring_add R x y))
            (@comm_ring_add S (f x) (f y))))
    (λ x : τ (@comm_ring_carrier R),
      @is_prop_pi
        (@comm_ring_carrier R)
        (λ y : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier S)
            (f (@comm_ring_add R x y))
            (@comm_ring_add S (f x) (f y)))
        (λ y : τ (@comm_ring_carrier R),
          (@comm_ring_carrier_is_set S)
            (f (@comm_ring_add R x y))
            (@comm_ring_add S (f x) (f y))));

symbol comm_ring_hom_preserves_neg_is_prop
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingHomPreservesNeg R S f))
≔ @is_prop_pi
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (f (@comm_ring_neg R x))
        (@comm_ring_neg S (f x)))
    (λ x : τ (@comm_ring_carrier R),
      (@comm_ring_carrier_is_set S)
        (f (@comm_ring_neg R x))
        (@comm_ring_neg S (f x)));

symbol comm_ring_hom_preserves_mul_is_prop
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingHomPreservesMul R S f))
≔ @is_prop_pi
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @Pi_grpd
        (@comm_ring_carrier R)
        (λ y : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier S)
            (f (@comm_ring_mul R x y))
            (@comm_ring_mul S (f x) (f y))))
    (λ x : τ (@comm_ring_carrier R),
      @is_prop_pi
        (@comm_ring_carrier R)
        (λ y : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier S)
            (f (@comm_ring_mul R x y))
            (@comm_ring_mul S (f x) (f y)))
        (λ y : τ (@comm_ring_carrier R),
          (@comm_ring_carrier_is_set S)
            (f (@comm_ring_mul R x y))
            (@comm_ring_mul S (f x) (f y))));

symbol comm_ring_hom_laws_is_prop
  [R S : τ CommRing]
  (f : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
  : τ (IsPropGrpd (@CommRingHomLaws R S f))
≔ @is_trunc_sigma
    trunc_minus_one
    (@CommRingHomPreservesZero R S f)
    (λ _ : τ (@CommRingHomPreservesZero R S f),
      `Σ_ one : τ (@CommRingHomPreservesOne R S f),
      `Σ_ add : τ (@CommRingHomPreservesAdd R S f),
      `Σ_ neg : τ (@CommRingHomPreservesNeg R S f),
          @CommRingHomPreservesMul R S f)
    (@comm_ring_hom_preserves_zero_is_prop R S f)
    (λ _ : τ (@CommRingHomPreservesZero R S f),
      @is_trunc_sigma
        trunc_minus_one
        (@CommRingHomPreservesOne R S f)
        (λ _ : τ (@CommRingHomPreservesOne R S f),
          `Σ_ add : τ (@CommRingHomPreservesAdd R S f),
          `Σ_ neg : τ (@CommRingHomPreservesNeg R S f),
              @CommRingHomPreservesMul R S f)
        (@comm_ring_hom_preserves_one_is_prop R S f)
        (λ _ : τ (@CommRingHomPreservesOne R S f),
          @is_trunc_sigma
            trunc_minus_one
            (@CommRingHomPreservesAdd R S f)
            (λ _ : τ (@CommRingHomPreservesAdd R S f),
              `Σ_ neg : τ (@CommRingHomPreservesNeg R S f),
                  @CommRingHomPreservesMul R S f)
            (@comm_ring_hom_preserves_add_is_prop R S f)
            (λ _ : τ (@CommRingHomPreservesAdd R S f),
              @is_trunc_sigma
                trunc_minus_one
                (@CommRingHomPreservesNeg R S f)
                (λ _ : τ (@CommRingHomPreservesNeg R S f),
                  @CommRingHomPreservesMul R S f)
                (@comm_ring_hom_preserves_neg_is_prop R S f)
                (λ _ : τ (@CommRingHomPreservesNeg R S f),
                  @comm_ring_hom_preserves_mul_is_prop R S f))));

symbol comm_ring_hom_function_is_set
  (R S : τ CommRing)
  : τ (IsSetGrpd (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)))
≔ @is_trunc_pi
    trunc_zero
    (@comm_ring_carrier R)
    (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier S)
    (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier_is_set S);

symbol comm_ring_hom_is_set
  (R S : τ CommRing)
  : τ (IsSetGrpd (@CommRingHom R S))
≔ @is_trunc_sigma
    trunc_zero
    (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))
    (λ f : τ (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)),
      @CommRingHomLaws R S f)
    (@comm_ring_hom_function_is_set R S)
    (λ f : τ (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)),
      @prop_is_trunc_succ
        trunc_minus_one
        (@CommRingHomLaws R S f)
        (@comm_ring_hom_laws_is_prop R S f));

// Pointwise equality of the retained carrier functions.
symbol CommRingHomPointwisePath
  [R S : τ CommRing]
  (h k : τ (@CommRingHom R S))
  : Grpd
≔ @Pi_grpd
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier S)
        (@comm_ring_hom_apply R S h x)
        (@comm_ring_hom_apply R S k x));

// Property-valued law fibres transport uniquely along a function path.
symbol comm_ring_hom_laws_pathover
  [R S : τ CommRing]
  [f g : τ (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))]
  (hf : τ (@CommRingHomLaws R S f))
  (hg : τ (@CommRingHomLaws R S g))
  (p : τ (f = g))
  : τ (@PathOver
      (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S))
      (λ q : τ (@Function_grpd
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)),
        @CommRingHomLaws R S q)
      f g p hf hg)
≔ @ind_eqr
    (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))
    g
    (λ f0 : τ (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)),
      λ p0 : τ (f0 = g),
        @Pi_grpd
          (@CommRingHomLaws R S f0)
          (λ hf0 : τ (@CommRingHomLaws R S f0),
            @PathOver
              (@Function_grpd
                (@comm_ring_carrier R)
                (@comm_ring_carrier S))
              (λ q : τ (@Function_grpd
                  (@comm_ring_carrier R)
                  (@comm_ring_carrier S)),
                @CommRingHomLaws R S q)
              f0 g p0 hf0 hg))
    (λ hf0 : τ (@CommRingHomLaws R S g),
      @is_contr_center
        (@= (@CommRingHomLaws R S g) hf0 hg)
        ((@comm_ring_hom_laws_is_prop R S g) hf0 hg))
    f
    p
    hf;

// Structured ring maps are equal when their carrier functions agree
// pointwise. This consumer-justified theorem adds no package-eta rule.
symbol comm_ring_hom_ext
  [R S : τ CommRing]
  [h k : τ (@CommRingHom R S)]
  (p : τ (@CommRingHomPointwisePath R S h k))
  : τ (h = k)
≔ @Struct_sigma
    (@= (@Function_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))
      (@comm_ring_hom_function R S h)
      (@comm_ring_hom_function R S k))
    (λ q : τ (@= (@Function_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S))
        (@comm_ring_hom_function R S h)
        (@comm_ring_hom_function R S k)),
      @PathOver
        (@Function_grpd
          (@comm_ring_carrier R)
          (@comm_ring_carrier S))
        (λ f : τ (@Function_grpd
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)),
          @CommRingHomLaws R S f)
        (@comm_ring_hom_function R S h)
        (@comm_ring_hom_function R S k)
        q
        (@comm_ring_hom_laws R S h)
        (@comm_ring_hom_laws R S k))
    (@PiFunext
      (@comm_ring_carrier R)
      (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      (@comm_ring_hom_function R S k)
      p)
    (@comm_ring_hom_laws_pathover
      R S
      (@comm_ring_hom_function R S h)
      (@comm_ring_hom_function R S k)
      (@comm_ring_hom_laws R S h)
      (@comm_ring_hom_laws R S k)
      (@PiFunext
        (@comm_ring_carrier R)
        (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier S)
        (@comm_ring_hom_function R S h)
        (@comm_ring_hom_function R S k)
        p));

// Ordinary category of commutative rings and structured homomorphisms.
injective symbol CommRing_cat : Cat;

rule Obj CommRing_cat
  ↪ CommRing;

rule Hom_cat CommRing_cat $R $S
  ↪ Path_cat (@CommRingHom $R $S);

symbol comm_ring_hom_id
  (R : τ CommRing)
  : τ (@CommRingHom R R)
≔ @id CommRing_cat R;

/*
  Stable pointwise identity comparison.

  Generic `id` remains the whole-arrow runtime owner. The rigid map below
  exposes only the carrier function selected by the empty-variable polynomial
  algebra consumer. Its narrow `sigma_Fst` clause is a constructor projection
  beta and does not intercept arbitrary generic category identities.
*/
injective symbol comm_ring_hom_id_pointwise
  (R : τ CommRing)
  : τ (@CommRingHom R R);

rule sigma_Fst (@comm_ring_hom_id_pointwise $R)
  ↪ λ x : τ (@comm_ring_carrier $R), x;

// Proof-time comparison; neither whole map is the other's runtime normal form.
unif_rule
  @id CommRing_cat $R
  ≡ @comm_ring_hom_id_pointwise $R
  ↪ [ tt ≡ tt ];

symbol comm_ring_hom_id_pointwise_path
  (R : τ CommRing)
  : τ (@= (@CommRingHom R R)
      (@comm_ring_hom_id R)
      (@comm_ring_hom_id_pointwise R))
≔ @eq_refl
    (@CommRingHom R R)
    (@comm_ring_hom_id R);

symbol comm_ring_hom_comp
  [R S T : τ CommRing]
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  : τ (@CommRingHom R T)
≔ @comp_fapp0 CommRing_cat R S T g f;

/*
  Stable pointwise composition comparison.

  Generic `comp_fapp0` remains the whole-arrow runtime owner. The rigid map
  below exposes only the carrier function selected by the first iterated-
  localization consumer, and meets generic composition at proof time. The
  narrow `sigma_Fst` clause is a constructor projection beta; it does not
  intercept arbitrary generic category cuts.
*/
injective symbol comm_ring_hom_comp_pointwise
  [R S T : τ CommRing]
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  : τ (@CommRingHom R T);

rule sigma_Fst
    (@comm_ring_hom_comp_pointwise $R $S $T $g $f)
  ↪ λ x : τ (@comm_ring_carrier $R),
      @comm_ring_hom_apply $S $T $g
        (@comm_ring_hom_apply $R $S $f x);

// Proof-time comparison; neither whole map is the other's runtime normal form.
unif_rule
  @comp_fapp0 CommRing_cat $R $S $T $g $f
  ≡ @comm_ring_hom_comp_pointwise $R $S $T $g $f
  ↪ [ tt ≡ tt ];

// Named theorem view of the proof-time comparison for downstream transport.
symbol comm_ring_hom_comp_pointwise_path
  [R S T : τ CommRing]
  (g : τ (@CommRingHom S T))
  (f : τ (@CommRingHom R S))
  : τ (@= (@CommRingHom R T)
      (@comm_ring_hom_comp R S T g f)
      (@comm_ring_hom_comp_pointwise R S T g f))
≔ @eq_refl
    (@CommRingHom R T)
    (@comm_ring_hom_comp R S T g f);

symbol comm_ring_cat_is_one_cat
  : τ (IsNCat (cat_succ cat_zero) CommRing_cat)
≔ λ R : τ CommRing,
    λ S : τ CommRing,
      @discrete_cat_intro
        (Path_cat (@CommRingHom R S))
        (@comm_ring_hom_is_set R S)
        (@path_cat_is_groupoidal (@CommRingHom R S));


/*
  A full carrier functor is deliberately absent. The transparent projection of
  a generic CommRing_cat identity/composite still does not compute pointwise.
  The selected rigid composition comparison above is the only pointwise cut
  view: forcing the behavior through broad sigma_Fst(id/comp_fapp0) clauses
  creates an outer-eliminator/inner-cut performance and overlap hazard.
*/
