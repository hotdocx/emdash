/*
  Reviewer for whole extension, matching, and section families over eligible
  ordinary covers.
*/

require open emdash.emdash3_2_direct_cover_question_families;

// A literal question evaluates to its existing ordinary-sieve extension.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @fapp0
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@Psh_cat K)
    (@direct_cover_question_extension_func K T)
    (Struct_sigma U q)
  ≡ @direct_cover_question_extension_psh K T U q;

// The companion varying representable retains the selected base object.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @fapp0
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@Psh_cat K)
    (@direct_cover_question_representable_func K T)
    (Struct_sigma U q)
  ≡ @yoneda_psh K U;

// The whole inclusion component reuses the deployed ordinary owner exactly.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @tapp0_fapp0
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@Psh_cat K)
    (@direct_cover_question_extension_func K T)
    (@direct_cover_question_representable_func K T)
    (Struct_sigma U q)
    (@direct_cover_question_extension_inclusion_transf K T)
  ≡ @direct_cover_question_extension_inclusion K T U q;

// Matching-family fibres are the existing whole presheaf hom-categories.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @Fibre_cat
    (@DirectCoverQuestion_cat K T)
    (@DirectCoverQuestionMatching_catd K T X)
    (Struct_sigma U q)
  ≡ @DirectCoverMatching_cat
      K U (@direct_cover_question_sieve K T U q) X;

// Section fibres are the existing Yoneda-section hom-categories.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @Fibre_cat
    (@DirectCoverQuestion_cat K T)
    (@DirectCoverQuestionSection_catd K T X)
    (Struct_sigma U q)
  ≡ @DirectCoverSection_cat K U X;

// Whole restriction evaluates to exact ordinary-sieve precomposition.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @tapp0_fapp0
    (@DirectCoverQuestion_cat K T)
    Cat_cat
    (@DirectCoverQuestionSection_catd K T X)
    (@DirectCoverQuestionMatching_catd K T X)
    (Struct_sigma U q)
    (@direct_cover_question_restriction_funcd K T X)
  ≡ @ordinary_sieve_local_precomp
      K U (@direct_cover_question_sieve K T U q) X;
