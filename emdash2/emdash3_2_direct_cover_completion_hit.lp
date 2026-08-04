/*
  Direct cover-indexed free-completion categorical-HIT boundary.

  For a site (K,T) and one Cat-valued presheaf P, this primitive whole
  presheaf is generated in the return/cover/silent shape

    eta      : P -> X,
    glue_q   : Functor(Hom(R_hat,X),Hom(y(U),X)),
    glue_all : Functord_Q(Match_X,Sect_X),
    silent   : glue_all o restriction_all = id

  Here R is a covering ordinary sieve and i_R:R_hat->y(U) is the existing
  whole sieve-extension inclusion.  A matching family is therefore one whole
  presheaf map.  Each glue component is a whole functor on the matching
  hom-category, while `glue_all` is one displayed functor over the internal
  eligible-question category.  Matching-arrow action, question pullback
  action, and both naturality dimensions therefore remain at generic owners.
  Silent is one path between whole displayed functors over that same internal
  question category.  Its literal-cover and pointwise observations are
  derived and are not runtime glue rewrites.

  At a canonical pullback question, generic whole strict naturality now
  derives the internal substitution path comparing transport-after-glue with
  glue-after-transport.  The whole glue and whole silent owners package the
  completion as a syntactic `DirectCoverSheaf`; this is the internal
  Pédrot-style algebraic notion, not yet the conventional two-sided
  restriction equivalence.  This boundary deliberately does not yet derive
  that comparison, topology-locality, the whole Hom universal property,
  functorial assembly on presheaf arrows, comparison with the rigid Sheaf_cat
  facade, a CommRing lift, or left exactness.  It is consequently named direct
  cover completion, not a completed sheafification reflector.
  A directed/lax silent cell would define a distinct effectful completion and
  is not introduced without a consumer.
*/

require open emdash.emdash3_2_direct_cover_internal_sheaves;

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

/*
  Whole internal substitution of recursive glue along a canonical question
  pullback:

    Section[p] o glue_q = glue_(p*q) o Matching[p].

  This is a transparent specialization of generic strict `Functord`
  naturality at the whole `tapp1_func` owner.  It is not an external family of
  component squares and introduces no sheaf-specific rewrite or unifier.
*/
symbol direct_cover_completion_glue_pullback_agrees
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (q : τ (@DirectCoverQuestionData K T U))
  : τ (@=
      (Hom
        Cat_cat
        (@Fibre_cat
          (@DirectCoverQuestion_cat K T)
          (@DirectCoverQuestionMatching_catd
            K T (@DirectCoverCompletionPsh K T P))
          (Struct_sigma U q))
        (@Fibre_cat
          (@DirectCoverQuestion_cat K T)
          (@DirectCoverQuestionSection_catd
            K T (@DirectCoverCompletionPsh K T P))
          (Struct_sigma V
            (@direct_cover_question_internal_pullback K T V U p q))))
      (@functord_transport_lhs_func
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionMatching_catd
          K T (@DirectCoverCompletionPsh K T P))
        (@DirectCoverQuestionSection_catd
          K T (@DirectCoverCompletionPsh K T P))
        (@direct_cover_completion_glue_funcd K T P)
        (Struct_sigma U q)
        (Struct_sigma V
          (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_pullback_arrow K T V U p q))
      (@functord_transport_rhs_func
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionMatching_catd
          K T (@DirectCoverCompletionPsh K T P))
        (@DirectCoverQuestionSection_catd
          K T (@DirectCoverCompletionPsh K T P))
        (@direct_cover_completion_glue_funcd K T P)
        (Struct_sigma U q)
        (Struct_sigma V
          (@direct_cover_question_internal_pullback K T V U p q))
        (@direct_cover_question_pullback_arrow K T V U p q)))
≔ @functord_transport_strict_naturality
    (@DirectCoverQuestion_cat K T)
    (@DirectCoverQuestionMatching_catd
      K T (@DirectCoverCompletionPsh K T P))
    (@DirectCoverQuestionSection_catd
      K T (@DirectCoverCompletionPsh K T P))
    (@direct_cover_completion_glue_funcd K T P)
    (Struct_sigma U q)
    (Struct_sigma V
      (@direct_cover_question_internal_pullback K T V U p q))
    (@direct_cover_question_pullback_arrow K T V U p q);

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

// Whole displayed endofunctor obtained by restricting and then gluing over
// every internal eligible question at once.
symbol direct_cover_completion_silent_source_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionSection_catd
        K T (@DirectCoverCompletionPsh K T P))
      (@DirectCoverQuestionSection_catd
        K T (@DirectCoverCompletionPsh K T P)))
≔ @direct_cover_sheaf_silent_source_funcd
    K T
    (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_glue_funcd K T P);

// Identity displayed endofunctor on the internal section family.
symbol direct_cover_completion_silent_target_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionSection_catd
        K T (@DirectCoverCompletionPsh K T P))
      (@DirectCoverQuestionSection_catd
        K T (@DirectCoverCompletionPsh K T P)))
≔ @direct_cover_sheaf_silent_target_funcd
    K T (@DirectCoverCompletionPsh K T P);

/*
  Primitive whole silent quotient, fully internal in the eligible question:

    glue_all o restriction_all = id.

  This is the categorical-HIT path constructor.  It owns cover-pullback and
  matching-arrow coherence as one displayed-functor path; consumers project
  it rather than supplying per-question equations.
*/
constant symbol direct_cover_completion_silent_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@=
      (Obj (@Functord_cat
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionSection_catd
          K T (@DirectCoverCompletionPsh K T P))
        (@DirectCoverQuestionSection_catd
          K T (@DirectCoverCompletionPsh K T P))))
      (@direct_cover_completion_silent_source_funcd K T P)
      (@direct_cover_completion_silent_target_funcd K T P));

// The completion carries the internal Pédrot-style direct-cover sheaf data.
symbol direct_cover_completion_sheaf_structure
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@DirectCoverSheafStructure
      K T (@DirectCoverCompletionPsh K T P))
≔ @direct_cover_sheaf_structure_intro
    K T (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_glue_funcd K T P)
    (@direct_cover_completion_silent_funcd K T P);

// Literal-cover silent is a component observation of the one internal path.
symbol direct_cover_completion_silent
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
          K U (@DirectCoverCompletionPsh K T P))))
≔ @direct_cover_sheaf_structure_silent
    K T (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_sheaf_structure K T P)
    U R covers;

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
≔ @direct_cover_sheaf_structure_algebra
    K T (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_sheaf_structure K T P);

// Syntactic direct-cover sheaf produced by the HIT for this input presheaf.
symbol direct_cover_completion_sheaf
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  : τ (@DirectCoverSheaf K T)
≔ @direct_cover_sheaf_intro
    K T
    (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_sheaf_structure K T P);

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
