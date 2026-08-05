/*
  Reviewer for internal Pédrot-style direct-cover sheaf structures.

  Glue is one displayed functor over the internal eligible-question category,
  and silent is one path between displayed functors there.  Literal-cover
  observations and the older per-cover algebra are projections.  This file
  does not assert conventional two-sided restriction equivalence, equality
  with the rigid Sheaf_cat facade, or a sheafification reflector.
*/

require open emdash.emdash3_2_direct_cover_internal_sheaves;

// The sheaf-structure classifier is attached to one whole presheaf.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K)) ⊢
  @DirectCoverSheafStructure K T X
  : Grpd;

// Glue is retained as one whole displayed functor in every question.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X)) ⊢
  @direct_cover_sheaf_structure_glue_funcd K T X S
  : τ (@Functord
      (@DirectCoverQuestion_cat K T)
      (@DirectCoverQuestionMatching_catd K T X)
      (@DirectCoverQuestionSection_catd K T X));

// Silent is retained once as a path of whole displayed endofunctors.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X)) ⊢
  @direct_cover_sheaf_structure_silent_funcd K T X S
  : τ (@=
      (Obj (@Functord_cat
        (@DirectCoverQuestion_cat K T)
        (@DirectCoverQuestionSection_catd K T X)
        (@DirectCoverQuestionSection_catd K T X)))
      (@direct_cover_sheaf_silent_source_funcd
        K T X (@direct_cover_sheaf_structure_glue_funcd K T X S))
      (@direct_cover_sheaf_silent_target_funcd K T X));

// A literal cover receives its glue functor by internal component projection.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_sheaf_structure_glue_func K T X S U R covers
  : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X));

// Its literal silent equation is derived from the one whole path.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_sheaf_structure_silent K T X S U R covers
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
      (@id Cat_cat (@DirectCoverSection_cat K U X)));

// The deployed per-cover oracle is a forgetful view of the internal owner.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_glue_func
    K T X (@direct_cover_sheaf_structure_algebra K T X S)
    U R covers
  ≡ @direct_cover_sheaf_structure_glue_func K T X S U R covers;

// Total direct-cover sheaves transparently retain their underlying presheaf.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X)) ⊢
  @direct_cover_sheaf_underlying_psh
    K T (@direct_cover_sheaf_intro K T X S)
  ≡ X;

// The second projection transparently recovers the same internal structure.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (S : τ (@DirectCoverSheafStructure K T X)) ⊢
  @direct_cover_sheaf_structure
    K T (@direct_cover_sheaf_intro K T X S)
  ≡ S;
