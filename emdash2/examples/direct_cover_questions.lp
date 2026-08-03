/*
  Reviewer for whole internal ordinary-cover questions.

  Eligible questions are ordinary covering sieves in Path-valued fibres.
  Their whole base action owns coherence, while the selected sieve projection
  computes and the proof component agrees internally with topology pullback.
*/

require open emdash.emdash3_2_direct_cover_questions;

// Stable observers compute on literal eligible-question constructors.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (cover : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_question_sieve K T U (Struct_sigma R cover)
  ≡ R;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (cover : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_question_cover K T U (Struct_sigma R cover)
  ≡ cover;

// The selected observers remain internally identified with the Sigma view.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_sieve_sigma_agrees K T U q
  : τ (@=
      (@Sieve K U)
      (@direct_cover_question_sieve K T U q)
      (sigma_Fst q));

assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_cover_sigma_agrees K T U q
  : τ (@PathOver
      (@Sieve K U)
      (λ R : τ (@Sieve K U), @groth_topology_covers K T U R)
      (@direct_cover_question_sieve K T U q)
      (sigma_Fst q)
      (@direct_cover_question_sieve_sigma_agrees K T U q)
      (@direct_cover_question_cover K T U q)
      (sigma_Snd q));

// Eligible questions form one whole Path-valued family over Op(K).
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)] ⊢
  @Fibre_cat
    (Op_cat K)
    (@DirectCoverQuestionClassifier K T)
    U
  ≡ Path_cat (@DirectCoverQuestionData K T U);

// Pullback computes on the retained ordinary-sieve data.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_sieve K T V
    (@direct_cover_question_internal_pullback K T V U p q)
  ≡ @sieve_pullback K V U p
      (@direct_cover_question_sieve K T U q);

// The internal cover proof agrees with explicit topology stability.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  @direct_cover_question_cover_action_agrees K T V U p q
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
        (@direct_cover_question_cover K T U q)));

// Literal questions reuse the deployed ordinary-sieve extension exactly.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (cover : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_question_extension_psh K T U (Struct_sigma R cover)
  ≡ @ordinary_sieve_extension_psh K U R;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (cover : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_question_extension_inclusion
    K T U (Struct_sigma R cover)
  ≡ @ordinary_sieve_extension_inclusion K U R;

// The canonical question arrow retains the literal base arrow.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U)) ⊢
  sigma_Fst (@direct_cover_question_pullback_arrow K T V U p q)
  ≡ p;
