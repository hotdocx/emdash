/*
  Direct cover-indexed free-completion categorical-HIT boundary.

  For a site (K,T) and one Cat-valued presheaf P, this primitive whole
  presheaf is generated in the return/cover/silent shape

    eta      : P -> X,
    glue_q   : Functor(Hom(R_hat,X),Hom(y(U),X)),
    glue_all : Functord_Q(Match_X,Sect_X),
    silent   : glue_q o restriction_q = id.

  Here R is a covering ordinary sieve and i_R:R_hat->y(U) is the existing
  whole sieve-extension inclusion.  A matching family is therefore one whole
  presheaf map.  Each glue component is a whole functor on the matching
  hom-category, while `glue_all` is one displayed functor over the internal
  eligible-question category.  Matching-arrow action, question pullback
  action, and both naturality dimensions therefore remain at generic owners.
  Silent is a whole functor path; its pointwise observation is derived and is
  not a runtime glue rewrite.

  This first boundary deliberately does not yet supply the dependent/non-
  dependent eliminator, a selected runtime formula for extension/glue action
  under a canonical pullback question, the missing restriction-after-glue
  law, topology-locality, the whole Hom universal property, functorial
  assembly on presheaf arrows, comparison with the rigid Sheaf_cat facade, a
  CommRing lift, or left exactness.  It is consequently named direct cover
  completion, not constructed sheafification.  A directed/lax silent cell
  would define a distinct effectful completion and is not introduced without
  a consumer.
*/

require open emdash.emdash3_2_direct_cover_question_families;

// Primitive whole presheaf generated from P by recursive covering-sieve glue.
injective symbol DirectCoverCompletionPsh
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@Psh K);

// Whole return/unit constructor.
constant symbol direct_cover_completion_unit
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (Hom
      (@Psh_cat K)
      P
      (@DirectCoverCompletionPsh K T P));

/*
  Stable component of the recursive cover constructor at one literal eligible
  question.  It retains the deployed head consumed by the recursor; the whole
  displayed constructor below adds action under question pullback.
*/
injective symbol direct_cover_completion_glue_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@Functor
      (@DirectCoverMatching_cat
        K U R (@DirectCoverCompletionPsh K T P))
      (@DirectCoverSection_cat
        K U (@DirectCoverCompletionPsh K T P)));

/*
  Whole recursive cover constructor over the internal eligible-question
  category.  Its displayed action owns restriction/pullback naturality in the
  question index, while each component remains the whole functor above on
  matching-family arrows.  Thus neither dimension is an external equation.
*/
injective symbol direct_cover_completion_glue_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionMatching_catd
        K T (@DirectCoverCompletionPsh K T P))
      (@DirectCoverQuestionSection_catd
        K T (@DirectCoverCompletionPsh K T P)));

// Literal-question component: recover the deployed one-cover glue functor.
rule @tapp0_fapp0
      _ Cat_cat _ _
      (Struct_sigma $U $q)
      (@direct_cover_completion_glue_funcd $K $T $P)
  ↪ @direct_cover_completion_glue_func
      $K $T $P $U
      (@direct_cover_question_sieve $K $T $U $q)
      (@direct_cover_question_cover $K $T $U $q);

// Pointwise glue observation, derived from the whole glue functor.
symbol direct_cover_completion_glue
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (matching : τ (Hom
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@DirectCoverCompletionPsh K T P)))
  : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P))
≔ @fapp0
    (@DirectCoverMatching_cat
      K U R (@DirectCoverCompletionPsh K T P))
    (@DirectCoverSection_cat
      K U (@DirectCoverCompletionPsh K T P))
    (@direct_cover_completion_glue_func K T P U R covers)
    matching;

// Restrict a whole generated section along the exact extended-sieve inclusion.
symbol direct_cover_completion_restrict
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (section : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P)))
  : τ (Hom
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@DirectCoverCompletionPsh K T P))
≔ @fapp0
    (@DirectCoverSection_cat
      K U (@DirectCoverCompletionPsh K T P))
    (@DirectCoverMatching_cat
      K U R (@DirectCoverCompletionPsh K T P))
    (@ordinary_sieve_local_precomp
      K U R (@DirectCoverCompletionPsh K T P))
    section;

// Primitive whole silent quotient: glue after restriction is identity.
constant symbol direct_cover_completion_silent
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat
          K U (@DirectCoverCompletionPsh K T P))
        (@DirectCoverSection_cat
          K U (@DirectCoverCompletionPsh K T P)))
      (@comp_fapp0
        Cat_cat
        (@DirectCoverSection_cat
          K U (@DirectCoverCompletionPsh K T P))
        (@DirectCoverMatching_cat
          K U R (@DirectCoverCompletionPsh K T P))
        (@DirectCoverSection_cat
          K U (@DirectCoverCompletionPsh K T P))
        (@direct_cover_completion_glue_func K T P U R covers)
        (@ordinary_sieve_local_precomp
          K U R (@DirectCoverCompletionPsh K T P)))
      (@id Cat_cat
        (@DirectCoverSection_cat
          K U (@DirectCoverCompletionPsh K T P))));

/*
  Canonical whole algebra assembled from the primitive whole glue and silent
  constructors.  This keeps the recursive glue as a stable HIT head while
  preserving all matching-arrow action at the Functor owner.
*/
symbol direct_cover_completion_algebra
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@DirectCoverAlgebra
      K T (@DirectCoverCompletionPsh K T P))
≔ λ U : τ (Obj K),
    λ R : τ (@Sieve K U),
      λ covers : τ (@groth_topology_covers K T U R),
        @direct_cover_at_intro
          K U R (@DirectCoverCompletionPsh K T P)
          (@direct_cover_completion_glue_func K T P U R covers)
          (@direct_cover_completion_silent K T P U R covers);

// Pointwise silent observation, derived from the whole functor equality.
symbol direct_cover_completion_silent_at
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (section : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P)))
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@yoneda_psh K U)
        (@DirectCoverCompletionPsh K T P))
      (@direct_cover_completion_glue K T P U R covers
        (@direct_cover_completion_restrict K T P U R section))
      section)
≔ @eq_ap
    (Hom
      Cat_cat
      (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
      (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P)))
    (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P))
    (λ F : τ (Hom
        Cat_cat
        (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
        (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))),
      @fapp0
        (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
        (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
        F section)
    (@comp_fapp0
      Cat_cat
      (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
      (@DirectCoverMatching_cat K U R (@DirectCoverCompletionPsh K T P))
      (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P))
      (@direct_cover_completion_glue_func K T P U R covers)
      (@ordinary_sieve_local_precomp
        K U R (@DirectCoverCompletionPsh K T P)))
    (@id Cat_cat
      (@DirectCoverSection_cat K U (@DirectCoverCompletionPsh K T P)))
    (@direct_cover_completion_silent K T P U R covers);
