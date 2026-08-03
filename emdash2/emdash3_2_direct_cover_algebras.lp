/*
  Whole direct-cover oracle algebras for Cat-valued presheaves.

  At a covering ordinary sieve R on U, matching families in X and sections
  of X are the whole hom-categories

    Match_R(X) = Hom_Psh(R_hat,X),
    Sect_U(X)  = Hom_Psh(y(U),X).

  A direct-cover oracle is a whole functor Match_R(X)->Sect_U(X).  Its silent
  law is the whole equality saying that oracle after restriction is identity.
  Thus arrow action between matching families and all component naturality
  stay at generic functor owners; no objectwise coherence family is stored.

  Topology-locality supplies this algebra by selecting the left inverse of
  each restriction equivalence.  The converse is not asserted here: deriving
  the other inverse law requires the external/internal comparison using
  pulled covers and maximality after restriction along a sieve member.
*/

require open emdash.emdash3_2_sieve_extensions;

// Whole category of matching families on the extended ordinary sieve.
symbol DirectCoverMatching_cat
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (X : τ (@Psh K))
  : Cat
≔ @Hom_cat
    (@Psh_cat K)
    (@ordinary_sieve_extension_psh K U R)
    X;

// Whole category of sections over U, presented by Yoneda maps into X.
symbol DirectCoverSection_cat
  [K : Cat]
  (U : τ (Obj K))
  (X : τ (@Psh K))
  : Cat
≔ @Hom_cat (@Psh_cat K) (@yoneda_psh K U) X;

// One whole oracle and its whole constant-family/silent law at one cover.
symbol DirectCoverAt
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (X : τ (@Psh K))
  : Grpd
≔ `Σ_ glue : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X)),
    @=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U X))
      (@comp_fapp0
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U X)
        glue
        (@ordinary_sieve_local_precomp K U R X))
      (@id Cat_cat (@DirectCoverSection_cat K U X));

// Readable constructor for the transparent one-cover Sigma package.
symbol direct_cover_at_intro
  [K : Cat]
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  [X : τ (@Psh K)]
  (glue : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X)))
  (silent : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U X))
      (@comp_fapp0
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U X)
        glue
        (@ordinary_sieve_local_precomp K U R X))
      (@id Cat_cat (@DirectCoverSection_cat K U X))))
  : τ (@DirectCoverAt K U R X)
≔ @Struct_sigma
    (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X))
    (λ G : τ (@Functor
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U X)),
      @=
        (Hom
          Cat_cat
          (@DirectCoverSection_cat K U X)
          (@DirectCoverSection_cat K U X))
        (@comp_fapp0
          Cat_cat
          (@DirectCoverSection_cat K U X)
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverSection_cat K U X)
          G
          (@ordinary_sieve_local_precomp K U R X))
        (@id Cat_cat (@DirectCoverSection_cat K U X)))
    glue silent;

// Whole oracle projection at one cover.
symbol direct_cover_at_glue_func
  [K : Cat]
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  [X : τ (@Psh K)]
  (A : τ (@DirectCoverAt K U R X))
  : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X))
≔ sigma_Fst A;

// Whole silent-law projection at one cover.
symbol direct_cover_at_silent
  [K : Cat]
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  [X : τ (@Psh K)]
  (A : τ (@DirectCoverAt K U R X))
  : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U X))
      (@comp_fapp0
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U X)
        (@direct_cover_at_glue_func K U R X A)
        (@ordinary_sieve_local_precomp K U R X))
      (@id Cat_cat (@DirectCoverSection_cat K U X)))
≔ sigma_Snd A;

// Whole oracle structure selected at every covering ordinary sieve.
symbol DirectCoverAlgebra
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (@Sieve K U)
        (λ R : τ (@Sieve K U),
          @Pi_grpd
            (@groth_topology_covers K T U R)
            (λ _ : τ (@groth_topology_covers K T U R),
              @DirectCoverAt K U R X)));

// Selected one-cover package of a whole algebra.
symbol direct_cover_algebra_at
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (A : τ (@DirectCoverAlgebra K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@DirectCoverAt K U R X)
≔ A U R covers;

// Whole glue functor selected by an algebra at one cover.
symbol direct_cover_algebra_glue_func
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (A : τ (@DirectCoverAlgebra K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X))
≔ @direct_cover_at_glue_func
    K U R X (@direct_cover_algebra_at K T X A U R covers);

// Whole silent equality selected by an algebra at one cover.
symbol direct_cover_algebra_silent
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (A : τ (@DirectCoverAlgebra K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U X))
      (@comp_fapp0
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U X)
        (@direct_cover_algebra_glue_func K T X A U R covers)
        (@ordinary_sieve_local_precomp K U R X))
      (@id Cat_cat (@DirectCoverSection_cat K U X)))
≔ @direct_cover_at_silent
    K U R X (@direct_cover_algebra_at K T X A U R covers);

/*
  A full restriction equivalence forgets to its selected left inverse and
  whole left law.  No new inverse, rewrite, or unification rule is introduced.
*/
symbol topology_local_direct_cover_algebra
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T X))
  : τ (@DirectCoverAlgebra K T X)
≔ λ U : τ (Obj K),
    λ R : τ (@Sieve K U),
      λ covers : τ (@groth_topology_covers K T U R),
        @direct_cover_at_intro
          K U R X
          (@omega_equiv_along_left_inv
            Cat_cat
            (@DirectCoverSection_cat K U X)
            (@DirectCoverMatching_cat K U R X)
            (@ordinary_sieve_local_precomp K U R X)
            (local U R covers))
          (@omega_equiv_along_left_law
            Cat_cat
            (@DirectCoverSection_cat K U X)
            (@DirectCoverMatching_cat K U R X)
            (@ordinary_sieve_local_precomp K U R X)
            (local U R covers));
