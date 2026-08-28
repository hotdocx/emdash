/*
  Cat-valued presheaves, Yoneda, slices, and Cat-valued higher sieves.

  This one-way standard-library module keeps `Psh_cat(K)` visible as the
  category of Cat-valued presheaves on K while reusing the active displayed-
  family hierarchy on K^op for all underlying computation.  The facade adds
  no independent functoriality or naturality calculus.
*/

require open emdash.emdash3_2;

/*
  Rigid category of Cat-valued presheaves.

  Surface/formula:
    Psh_cat(K) = K^op ⊢ Cat
    Psh(K)     = Obj(Psh_cat(K)).

  `Psh_cat(K)` and `Catd_cat(K^op)` remain distinct runtime heads.  Runtime
  access crosses through the object and hom projections below; their category
  comparison is deliberately proof-time only.
*/
injective symbol Psh_cat (K : Cat) : Cat;

// Runtime object projection: presheaves are Cat-valued families on K^op.
rule Obj (@Psh_cat $K)
  ↪ Obj (@Catd_cat (Op_cat $K));

// Runtime hom projection: presheaf maps are natural family morphisms.
rule Hom_cat (@Psh_cat $K) $P $Q
  ↪ @Functord_cat (Op_cat $K) $P $Q;

// Proof-time comparison only: recover the opposite base directly.
unif_rule
  @Psh_cat $K
  ≡ @Catd_cat $K0
  ↪ [ $K ≡ Op_cat $K0 ];

/*
  Whole proof-time coherence of public presheaf composition with the active
  displayed-family representation.  The generic category comparison above
  intentionally does not propagate through the rigid `comp_fapp0` head.
  Consumers that cross the facade therefore use this path explicitly; neither
  composition is selected as a runtime normal form for the other.
*/
constant symbol psh_comp_representation_agrees
  [K : Cat]
  [P Q R : τ (Obj (@Psh_cat K))]
  (g : τ (Hom (@Psh_cat K) Q R))
  (f : τ (Hom (@Psh_cat K) P Q))
  : τ (@=
      (Hom (@Psh_cat K) P R)
      (@comp_fapp0 (@Psh_cat K) P Q R g f)
      (@comp_catd_fapp0 (Op_cat K) P Q R g f));

// Object/type classifier of Cat-valued presheaves on K.
symbol Psh (K : Cat) : Grpd
≔ Obj (@Psh_cat K);

/*
  Restriction of presheaves along an ordinary functor.

  Surface/formula:
    F^* : Psh_cat(B) ⊢ Psh_cat(A)
    F^*(P) = Pullback_catd(P,Op_func(F)).

  This is a transparent facade over the existing Catd reindexing functor.
  Its object action therefore computes through `Pullback_catd_func`; ordinary
  identity, composition, functor action, and naturality retain their generic
  owners.
*/
symbol Psh_pullback_func
  [A B : Cat]
  (F : τ (Functor A B))
  : τ (Functor (@Psh_cat B) (@Psh_cat A))
≔ @Pullback_catd_func
    (Op_cat A)
    (Op_cat B)
    (@Op_func A B F);

/*
  Contravariant Yoneda through the existing internal-hom owner.

  Surface/formula:
    y_K       : K ⊢ Psh_cat(K)
    y_K(U)[V] = Hom_K(V,U).

  `hom_con_int(id_K)` already owns the object and arrow computations, so these
  declarations are transparent names rather than a second Yoneda calculus.
*/
symbol yoneda_psh_func
  (K : Cat)
  : τ (Functor K (@Psh_cat K))
≔ @hom_con_int K K (@id_func K);

symbol yoneda_psh
  [K : Cat]
  (U : τ (Obj K))
  : τ (Psh K)
≔ @fapp0 K (@Psh_cat K) (@yoneda_psh_func K) U;

/*
  Arrows into a varying object and the conventional slice.

  `arrow_into_catd(K)` is a directed Cat-valued family on K.  Its fibre
  `Into_restr_cat(U)` is Sigma_{V:K^op} Hom_K(V,U), whose direction is chosen
  for restriction.  The conventional slice K/U is its opposite.  Keeping
  both names visible prevents later site constructions from silently mixing
  the two variances.
*/
symbol arrow_into_catd (K : Cat) : τ (Catd K)
≔ @comp_cat_fapp0
    K
    (@Catd_cat (Op_cat K))
    Cat_cat
    (@Sigma_func (Op_cat K))
    (@yoneda_psh_func K);

symbol Into_restr_cat
  [K : Cat]
  (U : τ (Obj K))
  : Cat
≔ Fibre_cat (@arrow_into_catd K) U;

symbol Slice_cat
  [K : Cat]
  (U : τ (Obj K))
  : Cat
≔ Op_cat (@Into_restr_cat K U);

/*
  Whole domain projections for the restriction-oriented total and its
  conventional opposite slice.

  `Into_restr_cat(K,U)` is the Sigma total over `K^op`, so its generic Sigma
  projection lands in `K^op`. Taking the opposite gives the reusable whole
  domain functor `K/U → K`. These are generic slice operations; keeping them
  here prevents pullback/base-change and other consumers from depending on a
  commutative-algebra application module.
*/
symbol into_restr_domain_func
  [K : Cat]
  (U : τ (Obj K))
  : τ (Functor (@Into_restr_cat K U) (Op_cat K))
≔ @Sigma_proj1_func (Op_cat K) (@yoneda_psh K U);

symbol slice_domain_func
  [K : Cat]
  (U : τ (Obj K))
  : τ (Functor (@Slice_cat K U) K)
≔ @Op_func
    (@Into_restr_cat K U)
    (Op_cat K)
    (@into_restr_domain_func K U);

/*
  Stable domain of a conventional slice object.

  Generic slice objects need not be constructor-visible, so the whole domain
  functor and raw `sigma_Fst` projection intentionally remain distinct runtime
  histories. The stable head gives later pullback projections one exact source
  object; proof-time rules relate both semantic presentations without adding
  arbitrary Sigma eta or a global projection rewrite.
*/
injective symbol slice_object_domain
  [K : Cat]
  [U : τ (Obj K)]
  (f : τ (Obj (@Slice_cat K U)))
  : τ (Obj K);

// Constructor-visible slice object `(V,f)` has domain V.
rule @slice_object_domain _ _ (Struct_sigma $V $_)
  ↪ $V;

// Proof-time raw Sigma projection view.
unif_rule
  @slice_object_domain $K $U $f
  ≡ @sigma_Fst $A $B $f
  ↪ [
    $A ≡ (Obj (Op_cat $K));
    $B ≡ (λ V : τ (Obj (Op_cat $K)),
      Obj (@Fibre_cat (Op_cat $K) (@yoneda_psh $K $U) V))
  ];

/*
  Proof-time whole-domain observation after opposite action has exposed the
  underlying restriction-oriented Sigma projection.
*/
unif_rule
  @slice_object_domain $K $U $f
  ≡ @fapp0 $A $B $F $f
  ↪ [
    $A ≡ (@Into_restr_cat $K $U);
    $B ≡ (Op_cat $K);
    $F ≡ (@into_restr_domain_func $K $U)
  ];

/*
  Direct proof-time postcomposition-domain comparison. Opposite slice action
  has exposed the underlying Sigma map, whose first projection is unchanged.
  This one-step rule avoids relying on nontransitive chaining through the
  separate raw-Sigma and whole-domain comparisons above.
*/
unif_rule
  @slice_object_domain $K $X $a
  ≡ @fapp0 _ _
    (@Sigma_proj1_func
      (Op_cat $K)
      (@hom_con $K $Y $K (@id Cat_cat $K)))
    (@fapp0 _ _
      (@sigma_map_func
        (Op_cat $K)
        (@hom_con $K $X $K (@id Cat_cat $K))
        (@hom_con $K $Y $K (@id Cat_cat $K))
        (@hom_con_int_postcomp_func
          $K $K (@id Cat_cat $K) $X $Y $p))
      $a)
  ↪ [ tt ≡ tt ];

// Stable structure arrow of a conventional slice object.
injective symbol slice_object_arrow
  [K : Cat]
  [U : τ (Obj K)]
  (f : τ (Obj (@Slice_cat K U)))
  : τ (Hom K (@slice_object_domain K U f) U);

// Constructor-visible structure-arrow projection.
rule @slice_object_arrow _ _ (Struct_sigma _ $f)
  ↪ $f;

// Proof-time raw Sigma second projection view.
unif_rule
  @slice_object_arrow $K $U $f
  ≡ @sigma_Snd $A $B $f
  ↪ [
    $A ≡ (Obj (Op_cat $K));
    $B ≡ (λ V : τ (Obj (Op_cat $K)),
      Obj (@Fibre_cat (Op_cat $K) (@yoneda_psh $K $U) V))
  ];

// Transparent whole-domain observation of a conventional slice morphism.
symbol slice_arrow_underlying_semantic
  [K : Cat]
  [U : τ (Obj K)]
  [q r : τ (Obj (@Slice_cat K U))]
  (h : τ (Hom (@Slice_cat K U) q r))
  : τ (Hom K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r))
≔ @fapp1_fapp0
    (@Slice_cat K U)
    K
    (@slice_domain_func K U)
    q r h;

/*
  Stable underlying ambient arrow of a conventional slice morphism.

  Opposite action reverses the endpoint order before exposing the underlying
  Sigma projection.  The stable head retains the conventional q→r reading for
  arbitrary slice arrows; the proof-time rule records the exact post-`Op`
  semantic observation without a runtime fold.
*/
injective symbol slice_arrow_underlying
  [K : Cat]
  [U : τ (Obj K)]
  [q r : τ (Obj (@Slice_cat K U))]
  (h : τ (Hom (@Slice_cat K U) q r))
  : τ (Hom K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r));

// Constructor-visible ambient-arrow projection.
rule @slice_arrow_underlying
      _ _
      (Struct_sigma _ _)
      (Struct_sigma _ _)
      (Struct_sigma $p _)
  ↪ $p;

unif_rule
  @slice_arrow_underlying $K $U $q $r $h
  ≡ @fapp1_fapp0 $Into (Op_cat $K) $Domain $r $q $h
  ↪ [
    $Into ≡ (@Into_restr_cat $K $U);
    $Domain ≡ (@into_restr_domain_func $K $U)
  ];

/*
  Retained directed triangle of a slice arrow:

    arrow(r) ∘ underlying(h) ⇒ arrow(q).

  Arbitrary slice homs do not runtime-expand to their Sigma presentation, so
  this stable projection is required for whole counit and pullback-square
  consumers. The sole beta remains constructor-visible.
*/
injective symbol slice_arrow_cell
  [K : Cat]
  [U : τ (Obj K)]
  [q r : τ (Obj (@Slice_cat K U))]
  (h : τ (Hom (@Slice_cat K U) q r))
  : τ (Hom
      (Hom_cat K (@slice_object_domain K U q) U)
      (@comp_fapp0
        K
        (@slice_object_domain K U q)
        (@slice_object_domain K U r)
        U
        (@slice_object_arrow K U r)
        (@slice_arrow_underlying K U q r h))
      (@slice_object_arrow K U q));

// Constructor-visible triangle projection; its one projection warning is
// classified and does not introduce a critical pair.
rule @slice_arrow_cell
      _ _
      (Struct_sigma _ _)
      (Struct_sigma _ _)
      (Struct_sigma _ $alpha)
  ↪ $alpha;

/*
  Stable constructor for an arbitrary conventional-slice arrow.

  Raw `sigma_arrow` remains the constructor-visible implementation. Generic
  slice objects need not Sigma-expand, so this constructor accepts exactly
  the stable record data: an ambient arrow p and its directed triangle
  arrow(r) ∘ p ⇒ arrow(q). There is deliberately no arbitrary-arrow eta rule.
*/
injective symbol slice_arrow_intro
  [K : Cat]
  [U : τ (Obj K)]
  [q r : τ (Obj (@Slice_cat K U))]
  (p : τ (Hom K
      (@slice_object_domain K U q)
      (@slice_object_domain K U r)))
  (alpha : τ (Hom
      (Hom_cat K (@slice_object_domain K U q) U)
      (@comp_fapp0
        K
        (@slice_object_domain K U q)
        (@slice_object_domain K U r)
        U
        (@slice_object_arrow K U r)
        p)
      (@slice_object_arrow K U q)))
  : τ (Hom (@Slice_cat K U) q r);

rule @slice_arrow_underlying
      _ _ _ _
      (@slice_arrow_intro $K $U $q $r $p $alpha)
  ↪ $p;

rule @slice_arrow_cell
      _ _ _ _
      (@slice_arrow_intro $K $U $q $r $p $alpha)
  ↪ $alpha;

/*
  Cat-valued higher sieves.

  A higher sieve on U is a Cat-valued family on the restriction-oriented
  arrow category Into_restr_cat(U), equivalently a Cat-valued presheaf on the
  conventional slice K/U.  This is intentionally not the ordinary notion of
  a sieve as a subterminal Set-valued presheaf.  The downstream
  `emdash3_2_sieves` module owns the ordinary `Sieve` specialization; `Omega`
  remains reserved pending setness and contravariant-family assembly.

  The comparison with `Psh_cat(Slice_cat(U))` goes through the stable shared
  presentation `Catd_cat(Into_restr_cat(U))`; no direct conversion rule is
  installed merely to make unification transitive.
*/
symbol HigherSieveClassifier (K : Cat) : τ (Psh K)
≔ @Catd_catd_con K (@arrow_into_catd K);

symbol HigherSieve_cat
  [K : Cat]
  (U : τ (Obj K))
  : Cat
≔ Fibre_cat (@HigherSieveClassifier K) U;

symbol HigherSieve
  [K : Cat]
  (U : τ (Obj K))
  : Grpd
≔ Obj (@HigherSieve_cat K U);

// The maximal higher sieve is the terminal family on Into_restr_cat(U).
symbol maximal_higher_sieve
  [K : Cat]
  (U : τ (Obj K))
  : τ (@HigherSieve K U)
≔ @Terminal_catd (@Into_restr_cat K U);

// Restriction along p : V -> U, inherited from the classifier's action.
symbol HigherSieve_pullback_func
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  : τ (Functor
      (@HigherSieve_cat K U)
      (@HigherSieve_cat K V))
≔ @fapp1_fapp0
    (Op_cat K)
    Cat_cat
    (@HigherSieveClassifier K)
    U V p;

symbol higher_sieve_pullback
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  : τ (@HigherSieve K V)
≔ @fapp0
    (@HigherSieve_cat K U)
    (@HigherSieve_cat K V)
    (@HigherSieve_pullback_func K V U p)
    S;

/*
  Postcomposition in the restriction-oriented arrow total.

  This is the same `arrow_into_catd` action already used by higher-sieve
  pullback.  Naming the functor and its object action exposes the canonical
  arrow image to ordinary-sieve membership consumers without defining a
  second slice/sieve action.
*/
symbol into_restr_postcompose_func
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  : τ (Functor
      (@Into_restr_cat K V)
      (@Into_restr_cat K U))
≔ @fapp1_fapp0 K Cat_cat (@arrow_into_catd K) V U p;

symbol into_restr_postcompose
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (f : τ (Obj (@Into_restr_cat K V)))
  : τ (Obj (@Into_restr_cat K U))
≔ @fapp0
    (@Into_restr_cat K V)
    (@Into_restr_cat K U)
    (@into_restr_postcompose_func K V U p)
    f;

/*
  Constructor-level comparison with another composite-arrow presentation.

  For f : W -> V and p : V -> U, the canonical image of `(W,f)` retains the
  stable represented postcomposition point.  An explicit equality from
  another arrow g : W -> U to that point gives a directed arrow from `(W,g)`
  to the canonical image.  This is theorem-level transport through the
  existing Sigma and core-inclusion owners; it adds no computation rule.
*/
symbol into_restr_postcompose_constructor_arrow
  [K : Cat]
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (f : τ (Hom K W V))
  (g : τ (Hom K W U))
  (q : τ (@=
      (Hom K W U)
      g
      (@hom_postcomp_fapp0
        K K (@id_func K)
        W V U p f)))
  : τ (Hom
      (@Into_restr_cat K U)
      (@Struct_sigma
        (Obj (Op_cat K))
        (λ X : τ (Obj (Op_cat K)),
          Obj (@Fibre_cat (Op_cat K) (@yoneda_psh K U) X))
        W g)
      (@into_restr_postcompose
        K V U p
        (@Struct_sigma
          (Obj (Op_cat K))
          (λ X : τ (Obj (Op_cat K)),
            Obj (@Fibre_cat (Op_cat K) (@yoneda_psh K V) X))
          W f)))
≔ @sigma_arrow
    (Op_cat K)
    (@yoneda_psh K U)
    W W
    g
    (@hom_postcomp_fapp0
      K K (@id_func K)
      W V U p f)
    (@id (Op_cat K) W)
    (@path_to_hom
      (@Fibre_cat (Op_cat K) (@yoneda_psh K U) W)
      g
      (@hom_postcomp_fapp0
        K K (@id_func K)
        W V U p f)
      q);
