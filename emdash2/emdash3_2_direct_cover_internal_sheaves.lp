/*
  Internal Pédrot-style direct-cover sheaf structures.

  For one site (K,T) and one Cat-valued presheaf X, all eligible covering
  questions form the internal category Q = DirectCoverQuestion_cat(K,T).
  Matching families and sections are displayed Cat-valued families over Q,
  and restriction is one displayed functor between them.  A direct-cover
  sheaf structure consists of

    glue_all : Functord_Q(Matching_X,Section_X),
    silent   : glue_all o restriction_all = id_Section.

  In particular, neither glue nor silent is stored as an external family over
  objects, sieves, cover proofs, or naturality squares.  Literal-cover data are
  projections of these two whole internal owners.

  This is the categorical analogue of Pédrot's algebraic `isSh` signature and
  is sufficient to package the output of the direct cover-completion HIT as a
  syntactic direct-cover sheaf.  It is deliberately not definitionally
  identified with the separately supplied rigid `Sheaf_cat` facade.
  Conventional two-sided `IsTopologyLocalPsh` for the completion is derived
  downstream in `emdash3_2_direct_cover_completion_locality.lp`; it is not an
  additional field of this algebraic sheaf structure.
*/

require open emdash.emdash3_2_direct_cover_question_families;

// Restrict and then glue over every internal eligible question at once.
symbol direct_cover_sheaf_silent_source_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (glue : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionMatching_catd K T X)
      (@DirectCoverQuestionSection_catd K T X)))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionSection_catd K T X)
      (@DirectCoverQuestionSection_catd K T X))
≔ @comp_catd_fapp0
    (@DirectCoverQuestion_cat K T)
    (@DirectCoverQuestionSection_catd K T X)
    (@DirectCoverQuestionMatching_catd K T X)
    (@DirectCoverQuestionSection_catd K T X)
    glue
    (@direct_cover_question_restriction_funcd K T X);

// Identity displayed endofunctor on the internal section family.
symbol direct_cover_sheaf_silent_target_funcd
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionSection_catd K T X)
      (@DirectCoverQuestionSection_catd K T X))
≔ @id_funcd
    (@DirectCoverQuestion_cat K T)
    (@DirectCoverQuestionSection_catd K T X);

/*
  One whole internal glue operation and one whole silent path.  Question
  reindexing, matching-arrow action, and their coherence are inherited from
  the displayed-functor and equality owners rather than repeated as fields.
*/
symbol DirectCoverSheafStructure
  [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  : Grpd
≔ `Σ_ glue : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionMatching_catd K T X)
      (@DirectCoverQuestionSection_catd K T X)),
    @=
      (Obj (@Functord_cat
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionSection_catd K T X)
        (@DirectCoverQuestionSection_catd K T X)))
      (@direct_cover_sheaf_silent_source_funcd K T X glue)
      (@direct_cover_sheaf_silent_target_funcd K T X);

// Readable constructor for the transparent internal sheaf-structure package.
symbol direct_cover_sheaf_structure_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (glue : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionMatching_catd K T X)
      (@DirectCoverQuestionSection_catd K T X)))
  (silent : τ (@=
      (Obj (@Functord_cat
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionSection_catd K T X)
        (@DirectCoverQuestionSection_catd K T X)))
      (@direct_cover_sheaf_silent_source_funcd K T X glue)
      (@direct_cover_sheaf_silent_target_funcd K T X)))
  : τ (@DirectCoverSheafStructure K T X)
≔ Struct_sigma glue silent;

// Whole internal glue projection.
symbol direct_cover_sheaf_structure_glue_funcd
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (S : τ (@DirectCoverSheafStructure K T X))
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionMatching_catd K T X)
      (@DirectCoverQuestionSection_catd K T X))
≔ sigma_Fst S;

// Whole internal silent-path projection.
symbol direct_cover_sheaf_structure_silent_funcd
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (S : τ (@DirectCoverSheafStructure K T X))
  : τ (@=
      (Obj (@Functord_cat
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionSection_catd K T X)
        (@DirectCoverQuestionSection_catd K T X)))
      (@direct_cover_sheaf_silent_source_funcd
        K T X (@direct_cover_sheaf_structure_glue_funcd K T X S))
      (@direct_cover_sheaf_silent_target_funcd K T X))
≔ sigma_Snd S;

// Literal-cover glue is a component of the one whole displayed functor.
symbol direct_cover_sheaf_structure_glue_func
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (S : τ (@DirectCoverSheafStructure K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X))
≔ @tapp0_fapp0
    (@DirectCoverQuestion_cat K T)
    Cat_cat
    (@DirectCoverQuestionMatching_catd K T X)
    (@DirectCoverQuestionSection_catd K T X)
    (Struct_sigma U (Struct_sigma R covers))
    (@direct_cover_sheaf_structure_glue_funcd K T X S);

// Literal-cover silent is a component of the one whole internal path.
symbol direct_cover_sheaf_structure_silent
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (S : τ (@DirectCoverSheafStructure K T X))
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
        (@direct_cover_sheaf_structure_glue_func K T X S U R covers)
        (@ordinary_sieve_local_precomp K U R X))
      (@id Cat_cat (@DirectCoverSection_cat K U X)))
≔ @eq_ap
    (Obj (@Functord_cat
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionSection_catd K T X)
      (@DirectCoverQuestionSection_catd K T X)))
    (Hom
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverSection_cat K U X))
    (λ H : τ (@Functord
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionSection_catd K T X)
        (@DirectCoverQuestionSection_catd K T X)),
      @tapp0_fapp0
        (@DirectCoverQuestion_cat K T)
        Cat_cat
        (@DirectCoverQuestionSection_catd K T X)
        (@DirectCoverQuestionSection_catd K T X)
        (Struct_sigma U (Struct_sigma R covers))
        H)
    (@direct_cover_sheaf_silent_source_funcd
      K T X (@direct_cover_sheaf_structure_glue_funcd K T X S))
    (@direct_cover_sheaf_silent_target_funcd K T X)
    (@direct_cover_sheaf_structure_silent_funcd K T X S);

/*
  Forget the single internal owner to the earlier per-cover oracle interface.
  This adapter is for the deployed recursor; it does not reverse the ownership
  direction or add a second family of primitive glue/silent fields.
*/
symbol direct_cover_sheaf_structure_algebra
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X : τ (@Psh K)]
  (S : τ (@DirectCoverSheafStructure K T X))
  : τ (@DirectCoverAlgebra K T X)
≔ λ U : τ (Obj K),
    λ R : τ (@Sieve K U),
      λ covers : τ (@groth_topology_covers K T U R),
        @direct_cover_at_intro
          K U R X
          (@direct_cover_sheaf_structure_glue_func K T X S U R covers)
          (@direct_cover_sheaf_structure_silent K T X S U R covers);

// A syntactic direct-cover sheaf is a presheaf with the internal structure.
symbol DirectCoverSheaf
  [K : Cat]
  (T : τ (@GrothTopology K))
  : Grpd
≔ `Σ_ X : τ (@Psh K), @DirectCoverSheafStructure K T X;

// Readable constructor for the transparent total package.
symbol direct_cover_sheaf_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X))
  : τ (@DirectCoverSheaf K T)
≔ Struct_sigma X S;

// Underlying whole presheaf of a syntactic direct-cover sheaf.
symbol direct_cover_sheaf_underlying_psh
  [K : Cat]
  [T : τ (@GrothTopology K)]
  (S : τ (@DirectCoverSheaf K T))
  : τ (@Psh K)
≔ sigma_Fst S;

// Internal sheaf structure carried by the total package.
symbol direct_cover_sheaf_structure
  [K : Cat]
  [T : τ (@GrothTopology K)]
  (S : τ (@DirectCoverSheaf K T))
  : τ (@DirectCoverSheafStructure
      K T (@direct_cover_sheaf_underlying_psh K T S))
≔ sigma_Snd S;
