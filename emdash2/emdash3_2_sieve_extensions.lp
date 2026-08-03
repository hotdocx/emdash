/*
  Ordinary sieves as whole subpresheaf maps and topology-local presheaves.

  An ordinary sieve R on U is stored natively as a subterminal family over
  the restriction-oriented slice K/U.  Fibrewise dependent sum extends it to
  the ambient presheaf

    R_hat[V] = Sigma(f : Hom_K(V,U)), R(f),

  and the generic first projection is the whole inclusion R_hat -> y(U).
  Thus a Cat-valued presheaf X is local at R when precomposition by that exact
  inclusion is an `OmegaEquivAlong Cat_cat`.  Topology-locality quantifies the
  same whole condition over every selected covering sieve.

  The construction keeps all presheaf action and naturality at whole internal
  owners.  It does not construct a reflector or sheafification, identify the
  rigid `Sheaf_cat` facade, prove equivalence with weighted-limit descent,
  specialize to sets, or add component coherence fields.
*/

require open emdash.emdash3_2_sites;
require open emdash.emdash3_2_fibrewise_sigma;

// Dependent-sum extension of an ordinary sieve to the ambient presheaf base.
symbol ordinary_sieve_extension_psh
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : τ (@Psh K)
≔ @FibrewiseSigma_catd
    (Op_cat K)
    (@yoneda_psh K U)
    (@sieve_higher K U R);

// Whole inclusion R_hat -> y(U), inherited from fibrewise Sigma projection.
symbol ordinary_sieve_extension_inclusion
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : τ (Hom
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@yoneda_psh K U))
≔ @fibrewise_sigma_proj1_funcd
    (Op_cat K)
    (@yoneda_psh K U)
    (@sieve_higher K U R);

// Whole restriction of maps into X along the selected sieve inclusion.
symbol ordinary_sieve_local_precomp
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (X : τ (@Psh K))
  : τ (Functor
      (Hom_cat (@Psh_cat K) (@yoneda_psh K U) X)
      (Hom_cat
        (@Psh_cat K)
        (@ordinary_sieve_extension_psh K U R)
        X))
≔ @hom_precomp_along_func
    (@Psh_cat K)
    (@Psh_cat K)
    (@id_func (@Psh_cat K))
    X
    (@ordinary_sieve_extension_psh K U R)
    (@yoneda_psh K U)
    (@ordinary_sieve_extension_inclusion K U R);

// Locality at one ordinary sieve is one fixed-forward whole Hom equivalence.
symbol PshLocalAtOrdinarySieve
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (X : τ (@Psh K))
  : Grpd
≔ @OmegaEquivAlong
    Cat_cat
    (Hom_cat (@Psh_cat K) (@yoneda_psh K U) X)
    (Hom_cat
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      X)
    (@ordinary_sieve_local_precomp K U R X);

/*
  Topology-local Cat-valued presheaf. Coverhood indexes the whole locality
  condition; no propositional cover witness is converted into runtime data.
*/
symbol IsTopologyLocalPsh
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
              @PshLocalAtOrdinarySieve K U R X)));
