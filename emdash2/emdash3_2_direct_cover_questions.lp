/*
  Whole internal questions for ordinary covering-sieve descent.

  The computational question at U is a higher sieve S.  These questions
  already form the strict presheaf `HigherSieveClassifier(K)`, so pullback,
  identity, composition, and higher action stay at one existing whole owner.
  The statement that S is ordinary and covering is proposition-valued
  eligibility evidence over that question.

  Pullback computes on the higher-sieve data.  The eligibility family owns
  arbitrary action and coherence internally; at the canonical pullback arrow
  its action agrees propositionally with the explicit topology operation.
  No runtime proof reconstruction, external naturality square, ordinary-
  sieve package eta, glue operation, or sheafification claim is introduced.
*/

require open emdash.emdash3_2_sieve_extensions;

// Proposition-valued eligibility of one internal higher-sieve question.
symbol DirectCoverQuestionEvidence
  [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  : Grpd
≔ `Σ_ ordinary : τ (@IsOrdinarySieve K U S),
    @groth_topology_covers
      K T U (@sieve_intro K U S ordinary);

// Both retained eligibility witnesses are properties.
symbol direct_cover_question_evidence_is_prop
  [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  : τ (IsPropGrpd (@DirectCoverQuestionEvidence K T U S))
≔ @is_trunc_sigma
    trunc_minus_one
    (@IsOrdinarySieve K U S)
    (λ ordinary : τ (@IsOrdinarySieve K U S),
      @groth_topology_covers
        K T U (@sieve_intro K U S ordinary))
    (@is_ordinary_sieve_evidence_is_prop K U S)
    (λ ordinary : τ (@IsOrdinarySieve K U S),
      @covers_is_prop
        K
        (@groth_topology_cover_predicate K T)
        U
        (@sieve_intro K U S ordinary));

// Explicit pullback of eligibility through ordinary-sieve stability.
symbol direct_cover_question_evidence_pullback
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  (e : τ (@DirectCoverQuestionEvidence K T U S))
  : τ (@DirectCoverQuestionEvidence
      K T V (@higher_sieve_pullback K V U p S))
≔ @Struct_sigma
    (@IsOrdinarySieve
      K V (@higher_sieve_pullback K V U p S))
    (λ ordinary : τ (@IsOrdinarySieve
        K V (@higher_sieve_pullback K V U p S)),
      @groth_topology_covers
        K T V
        (@sieve_intro
          K V (@higher_sieve_pullback K V U p S) ordinary))
    (@ordinary_sieve_pullback_evidence
      K V U p S (sigma_Fst e))
    (@groth_topology_pullback
      K T U V p
      (@sieve_intro K U S (sigma_Fst e))
      (sigma_Snd e));

// Ambient dependent-sum extension of the higher-sieve question.
symbol direct_cover_question_extension_psh
  [K : Cat]
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  : τ (@Psh K)
≔ @FibrewiseSigma_catd
    (Op_cat K)
    (@yoneda_psh K U)
    S;

// Whole inclusion of that extension into the represented question object.
symbol direct_cover_question_extension_inclusion
  [K : Cat]
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U))
  : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K U S)
      (@yoneda_psh K U))
≔ @fibrewise_sigma_proj1_funcd
    (Op_cat K)
    (@yoneda_psh K U)
    S;

// Whole base of questions: dependent pairs (U,S) over the strict classifier.
symbol DirectCoverQuestion_cat
  (K : Cat)
  : Cat
≔ @Sigma_cat (Op_cat K) (@HigherSieveClassifier K);

// Canonical question arrow carrying S to its strict higher-sieve pullback.
symbol direct_cover_question_pullback_arrow
  [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  : τ (Hom
      (@DirectCoverQuestion_cat K)
      (Struct_sigma U S)
      (Struct_sigma V (@higher_sieve_pullback K V U p S)))
≔ @sigma_transport_arrow
    (Op_cat K)
    (@HigherSieveClassifier K)
    U V p S;

/*
  Whole eligibility family over all internal questions.  Its arbitrary arrow
  action and all higher coherence are owned here.  Only fibres compute; the
  proof-valued action is compared propositionally below.
*/
injective symbol DirectCoverQuestionEvidence_catd
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (Catd (@DirectCoverQuestion_cat K));

rule @fapp0
      _ Cat_cat
      (@DirectCoverQuestionEvidence_catd $K $T)
      (Struct_sigma $U $S)
  ↪ Path_cat (@DirectCoverQuestionEvidence $K $T $U $S);

/*
  At a canonical question pullback, internal evidence action agrees with the
  explicit topology operation.  The target is a proposition, so uniqueness
  derives the comparison without a runtime proof-reconstruction rule.
*/
symbol direct_cover_question_evidence_action_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  (e : τ (@DirectCoverQuestionEvidence K T U S))
  : τ (@=
      (@DirectCoverQuestionEvidence
        K T V (@higher_sieve_pullback K V U p S))
      (@fapp0
        (Path_cat (@DirectCoverQuestionEvidence K T U S))
        (Path_cat (@DirectCoverQuestionEvidence
          K T V (@higher_sieve_pullback K V U p S)))
        (@catd_transport_func
          (@DirectCoverQuestion_cat K)
          (@DirectCoverQuestionEvidence_catd K T)
          (Struct_sigma U S)
          (Struct_sigma V (@higher_sieve_pullback K V U p S))
          (@direct_cover_question_pullback_arrow K V U p S))
        e)
      (@direct_cover_question_evidence_pullback K T V U p S e))
≔ @is_contr_center
    (@=
      (@DirectCoverQuestionEvidence
        K T V (@higher_sieve_pullback K V U p S))
      (@fapp0
        (Path_cat (@DirectCoverQuestionEvidence K T U S))
        (Path_cat (@DirectCoverQuestionEvidence
          K T V (@higher_sieve_pullback K V U p S)))
        (@catd_transport_func
          (@DirectCoverQuestion_cat K)
          (@DirectCoverQuestionEvidence_catd K T)
          (Struct_sigma U S)
          (Struct_sigma V (@higher_sieve_pullback K V U p S))
          (@direct_cover_question_pullback_arrow K V U p S))
        e)
      (@direct_cover_question_evidence_pullback K T V U p S e))
    ((@direct_cover_question_evidence_is_prop
      K T V (@higher_sieve_pullback K V U p S))
      (@fapp0
        (Path_cat (@DirectCoverQuestionEvidence K T U S))
        (Path_cat (@DirectCoverQuestionEvidence
          K T V (@higher_sieve_pullback K V U p S)))
        (@catd_transport_func
          (@DirectCoverQuestion_cat K)
          (@DirectCoverQuestionEvidence_catd K T)
          (Struct_sigma U S)
          (Struct_sigma V (@higher_sieve_pullback K V U p S))
          (@direct_cover_question_pullback_arrow K V U p S))
        e)
      (@direct_cover_question_evidence_pullback K T V U p S e));
