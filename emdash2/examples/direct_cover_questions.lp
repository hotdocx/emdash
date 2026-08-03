/*
  Reviewer for whole internal covering questions.

  Higher-sieve data carries the strict pullback action.  Ordinary-sieve and
  coverhood evidence remains proposition-valued and agrees at proof time with
  the explicit topology operation; no external naturality family is stored.
*/

require open emdash.emdash3_2_direct_cover_questions;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U)) ⊢
  @direct_cover_question_evidence_is_prop K T U S
  : τ (IsPropGrpd (@DirectCoverQuestionEvidence K T U S));

assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  (e : τ (@DirectCoverQuestionEvidence K T U S)) ⊢
  @direct_cover_question_evidence_pullback K T V U p S e
  : τ (@DirectCoverQuestionEvidence
      K T V (@higher_sieve_pullback K V U p S));

// Ordinary-sieve consumers retain the exact deployed ambient extension.
assert [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U)) ⊢
  @direct_cover_question_extension_psh K U (@sieve_higher K U R)
  ≡ @ordinary_sieve_extension_psh K U R;

assert [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U)) ⊢
  @direct_cover_question_extension_inclusion
    K U (@sieve_higher K U R)
  ≡ @ordinary_sieve_extension_inclusion K U R;

// The canonical question arrow retains the literal base arrow.
assert [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U)) ⊢
  sigma_Fst (@direct_cover_question_pullback_arrow K V U p S)
  ≡ p;

// Eligibility is one whole displayed family over the question total.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (S : τ (@HigherSieve K U)) ⊢
  @Fibre_cat
    (@DirectCoverQuestion_cat K)
    (@DirectCoverQuestionEvidence_catd K T)
    (Struct_sigma U S)
  ≡ Path_cat (@DirectCoverQuestionEvidence K T U S);

// Its canonical action comparison is derived inside the target proposition.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (S : τ (@HigherSieve K U))
  (e : τ (@DirectCoverQuestionEvidence K T U S)) ⊢
  @direct_cover_question_evidence_action_agrees K T V U p S e
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
      (@direct_cover_question_evidence_pullback K T V U p S e));
