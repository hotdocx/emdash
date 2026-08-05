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
