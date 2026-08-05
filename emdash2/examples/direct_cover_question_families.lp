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

// Canonical pullback has the exact whole presheaf-map endpoint.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_extension_pullback_func K T V U p q
  : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh
        K T V (@direct_cover_question_internal_pullback K T V U p q))
      (@direct_cover_question_extension_psh K T U q));

// Its component is the selected stable fibre functor.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @tapp0_fapp0
    (Op_cat K)
    Cat_cat
    (@direct_cover_question_extension_psh
      K T V (@direct_cover_question_internal_pullback K T V U p q))
    (@direct_cover_question_extension_psh K T U q)
    W
    (@direct_cover_question_extension_pullback_func K T V U p q)
  ≡ @direct_cover_question_extension_pullback_fibre_func
      K T W V U p q;

// Literal extension elements postcompose their arrow and retain membership.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (h : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@direct_cover_question_sieve K T U q)
      (@into_restr_postcompose K V U p (Struct_sigma W h)))) ⊢
  @fapp0
    (@Fibre_cat
      (Op_cat K)
      (@direct_cover_question_extension_psh
        K T V (@direct_cover_question_internal_pullback K T V U p q))
      W)
    (@Fibre_cat
      (Op_cat K)
      (@direct_cover_question_extension_psh K T U q)
      W)
    (@direct_cover_question_extension_pullback_fibre_func
      K T W V U p q)
    (Struct_sigma h member)
  ≡ @direct_cover_question_extension_pullback_pair
      K T W V U p q h member;

// The opaque generic action agrees by one whole proof-time path.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_extension_pullback_agrees K T V U p q
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@direct_cover_question_extension_psh
          K T V (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_extension_psh K T U q))
      (@direct_cover_question_extension_pullback_generic K T V U p q)
      (@direct_cover_question_extension_pullback_func K T V U p q));

// Projecting the whole path yields the literal pair observation.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [W V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  (h : τ (Hom K W V))
  (member : τ (@SieveMembership
      K U
      (@direct_cover_question_sieve K T U q)
      (@into_restr_postcompose K V U p (Struct_sigma W h)))) ⊢
  @direct_cover_question_extension_pullback_pair_agrees
    K T W V U p q h member
  : τ (@=
      (Obj (@Fibre_cat
        (Op_cat K)
        (@direct_cover_question_extension_psh K T U q)
        W))
      (@fapp0
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          W)
        (@Fibre_cat
          (Op_cat K)
          (@direct_cover_question_extension_psh K T U q)
          W)
        (@tapp0_fapp0
          (Op_cat K) Cat_cat
          (@direct_cover_question_extension_psh
            K T V (@direct_cover_question_internal_pullback K T V U p q))
          (@direct_cover_question_extension_psh K T U q)
          W
          (@direct_cover_question_extension_pullback_generic K T V U p q))
        (Struct_sigma h member))
      (@direct_cover_question_extension_pullback_pair
        K T W V U p q h member));

// The semantic representable action already reduces to direct Yoneda action.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @fapp1_fapp0
    (Op_cat (@DirectCoverQuestion_cat K T))
    (@Psh_cat K)
    (@direct_cover_question_representable_func K T)
    (Struct_sigma V
      (@direct_cover_question_internal_pullback K T V U p q))
    (Struct_sigma U q)
    (@direct_cover_question_pullback_arrow K T V U p q)
  ≡ @fapp1_fapp0 K (@Psh_cat K) (@yoneda_psh_func K) V U p;

// The proof-time comparison deliberately does not add a competing runtime fold.
assertnot [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_extension_pullback_generic K T V U p q
  ≡ @direct_cover_question_extension_pullback_func K T V U p q;

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
