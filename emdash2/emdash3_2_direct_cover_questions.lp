/*
  Whole internal questions for ordinary covering-sieve descent.

  A question at U is an ordinary sieve R together with evidence that R covers
  U.  Ordinary sieves retain their Cat-valued higher-sieve carrier, but the
  question fibre is Path-valued: arbitrary higher-sieve transformations do
  not incorrectly transport ordinary-and-covering evidence.

  One whole family over Op(K) owns pullback, identity, composition, and all
  higher coherence.  Its stable sieve projection computes to ordinary-sieve
  pullback.  The transported cover proof stays internal and agrees by proof
  irrelevance with explicit Grothendieck pullback.  No external naturality
  square, runtime proof reconstruction, glue operation, or sheafification
  claim is introduced.
*/

require open emdash.emdash3_2_sieve_extensions;

// Eligible descent question at U: an ordinary covering sieve.
symbol DirectCoverQuestionData
  [K : Cat]
  (T : τ (@GrothTopology K))
  (U : τ (Obj K))
  : Grpd
≔ `Σ_ R : τ (@Sieve K U),
    @groth_topology_covers K T U R;

/*
  Stable projections are selected runtime observers for the question record.
  The paths below identify them internally with the underlying Sigma view.
*/
injective symbol direct_cover_question_sieve
  [K : Cat]
  (T : τ (@GrothTopology K))
  (U : τ (Obj K))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Sieve K U);

rule @direct_cover_question_sieve _ _ _ (Struct_sigma $R _)
  ↪ $R;

injective symbol direct_cover_question_cover
  [K : Cat]
  (T : τ (@GrothTopology K))
  (U : τ (Obj K))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@groth_topology_covers
      K T U (@direct_cover_question_sieve K T U q));

rule @direct_cover_question_cover _ _ _ (Struct_sigma _ $cover)
  ↪ $cover;

// The selected sieve observer agrees with ordinary Sigma projection.
symbol direct_cover_question_sieve_sigma_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  (U : τ (Obj K))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@=
      (@Sieve K U)
      (@direct_cover_question_sieve K T U q)
      (sigma_Fst q))
≔ @sigma_ind
    (@Sieve K U)
    (λ R : τ (@Sieve K U), @groth_topology_covers K T U R)
    (λ q : τ (@DirectCoverQuestionData K T U),
      @= (@Sieve K U)
        (@direct_cover_question_sieve K T U q)
        (sigma_Fst q))
    (λ R : τ (@Sieve K U),
      λ _ : τ (@groth_topology_covers K T U R),
        @eq_refl (@Sieve K U) R)
    q;

// The selected cover observer agrees dependently with Sigma projection.
symbol direct_cover_question_cover_sigma_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  (U : τ (Obj K))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@PathOver
      (@Sieve K U)
      (λ R : τ (@Sieve K U), @groth_topology_covers K T U R)
      (@direct_cover_question_sieve K T U q)
      (sigma_Fst q)
      (@direct_cover_question_sieve_sigma_agrees K T U q)
      (@direct_cover_question_cover K T U q)
      (sigma_Snd q))
≔ @prop_family_pathover
    (@Sieve K U)
    (λ R : τ (@Sieve K U), @groth_topology_covers K T U R)
    (λ R : τ (@Sieve K U),
      @covers_is_prop K (@groth_topology_cover_predicate K T) U R)
    (@direct_cover_question_sieve K T U q)
    (sigma_Fst q)
    (@direct_cover_question_sieve_sigma_agrees K T U q)
    (@direct_cover_question_cover K T U q)
    (sigma_Snd q);

/*
  Path-valued presheaf of eligible questions.  The primitive whole owner is
  justified by Grothendieck pullback stability; generic functor action owns
  its coherence.  Only its computational sieve observation is selected.
*/
injective symbol DirectCoverQuestionClassifier
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (Catd (Op_cat K));

rule @fapp0 _ Cat_cat (@DirectCoverQuestionClassifier $K $T) $U
  ↪ Path_cat (@DirectCoverQuestionData $K $T $U);

// Pullback computes on the ordinary-sieve part of an eligible question.
rule @direct_cover_question_sieve
      $K $T $V
      (@fapp0
        _
        _
        (@fapp1_fapp0
          (Op_cat $K)
          Cat_cat
          (@DirectCoverQuestionClassifier $K $T)
          $U $V $p)
        $q)
  ↪ @sieve_pullback
      $K $V $U $p (@direct_cover_question_sieve $K $T $U $q);

// The actual coherent pullback question selected by the whole family.
symbol direct_cover_question_internal_pullback
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@DirectCoverQuestionData K T V)
≔ @fapp0
    (Path_cat (@DirectCoverQuestionData K T U))
    (Path_cat (@DirectCoverQuestionData K T V))
    (@catd_transport_func
      (Op_cat K)
      (@DirectCoverQuestionClassifier K T)
      U V p)
    q;

/*
  The internally transported proof agrees with explicit topology pullback.
  This is equality evidence in a proposition, not a runtime proof-field rule.
*/
symbol direct_cover_question_cover_action_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@=
      (@groth_topology_covers
        K T V (@sieve_pullback K V U p
          (@direct_cover_question_sieve K T U q)))
      (@direct_cover_question_cover
        K T V
        (@direct_cover_question_internal_pullback K T V U p q))
      (@groth_topology_pullback
        K T U V p
        (@direct_cover_question_sieve K T U q)
        (@direct_cover_question_cover K T U q)))
≔ @is_contr_center
    (@=
      (@groth_topology_covers
        K T V (@sieve_pullback K V U p
          (@direct_cover_question_sieve K T U q)))
      (@direct_cover_question_cover
        K T V
        (@direct_cover_question_internal_pullback K T V U p q))
      (@groth_topology_pullback
        K T U V p
        (@direct_cover_question_sieve K T U q)
        (@direct_cover_question_cover K T U q)))
    ((@covers_is_prop
      K
      (@groth_topology_cover_predicate K T)
      V
      (@sieve_pullback K V U p
        (@direct_cover_question_sieve K T U q)))
      (@direct_cover_question_cover
        K T V
        (@direct_cover_question_internal_pullback K T V U p q))
      (@groth_topology_pullback
        K T U V p
        (@direct_cover_question_sieve K T U q)
        (@direct_cover_question_cover K T U q)));

// Ambient extension of the ordinary sieve selected by an eligible question.
symbol direct_cover_question_extension_psh
  [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@Psh K)
≔ @ordinary_sieve_extension_psh
    K U (@direct_cover_question_sieve K T U q);

// Whole inclusion of the selected extension into its representable object.
symbol direct_cover_question_extension_inclusion
  [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (Hom
      (@Psh_cat K)
      (@direct_cover_question_extension_psh K T U q)
      (@yoneda_psh K U))
≔ @ordinary_sieve_extension_inclusion
    K U (@direct_cover_question_sieve K T U q);

// Whole category of eligible questions varying contravariantly in the base.
symbol DirectCoverQuestion_cat
  [K : Cat]
  (T : τ (@GrothTopology K))
  : Cat
≔ @Sigma_cat (Op_cat K) (@DirectCoverQuestionClassifier K T);

// Canonical total arrow over p, using the family's actual pullback question.
symbol direct_cover_question_pullback_arrow
  [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (Hom
      (@DirectCoverQuestion_cat K T)
      (Struct_sigma U q)
      (Struct_sigma V
        (@direct_cover_question_internal_pullback K T V U p q)))
≔ @sigma_transport_arrow
    (Op_cat K)
    (@DirectCoverQuestionClassifier K T)
    U V p q;
