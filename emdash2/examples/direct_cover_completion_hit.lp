/*
  Reviewer for the direct eta/glue/silent cover-completion HIT boundary.

  Unit, matching data, and generated sections are whole presheaf maps.  Glue
  is a whole functor on matching families, and silent is one whole functor
  path whose pointwise observation is derived.  It deliberately does not
  collapse glue by runtime conversion.  No restriction-equivalence,
  sheafification, or reflector claim is made yet.
*/

require open emdash.emdash3_2_direct_cover_completion_hit;

// Formation stays at the whole Cat-valued presheaf owner.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K)) ⊢
  @DirectCoverCompletionPsh K T P
  : τ (@Psh K);

// The return constructor is one whole presheaf morphism.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K)) ⊢
  @direct_cover_completion_unit K T P
  : τ (Hom
      (@Psh_cat K)
      P
      (@DirectCoverCompletionPsh K T P));

// The completion carries one canonical whole oracle algebra.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K)) ⊢
  @direct_cover_completion_algebra K T P
  : τ (@DirectCoverAlgebra
      K T (@DirectCoverCompletionPsh K T P));

// Cover glue is a whole functor, including matching-arrow action.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_completion_glue_func K T P U R covers
  : τ (@Functor
      (@DirectCoverMatching_cat
        K U R (@DirectCoverCompletionPsh K T P))
      (@DirectCoverSection_cat
        K U (@DirectCoverCompletionPsh K T P)));

// The canonical algebra projects exactly to the primitive whole glue head.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_glue_func
    K T
    (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_algebra K T P)
    U R covers
  ≡ @direct_cover_completion_glue_func K T P U R covers;

// Cover glue consumes one internally compatible whole matching map.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (matching : τ (Hom
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@DirectCoverCompletionPsh K T P))) ⊢
  @direct_cover_completion_glue K T P U R covers matching
  : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P));

// Restriction is the object action of the exact whole precomposition functor.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (section : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P))) ⊢
  @direct_cover_completion_restrict K T P U R section
  ≡ @fapp0
      (@DirectCoverSection_cat
        K U (@DirectCoverCompletionPsh K T P))
      (@DirectCoverMatching_cat
        K U R (@DirectCoverCompletionPsh K T P))
      (@ordinary_sieve_local_precomp
        K U R (@DirectCoverCompletionPsh K T P))
      section;

// Silent is one first-class equality of whole section endofunctors.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_completion_silent K T P U R covers
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

// Its silent projection is exactly the primitive whole silent path.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_silent
    K T
    (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_algebra K T P)
    U R covers
  ≡ @direct_cover_completion_silent K T P U R covers;

// The former pointwise silent path is derived from that whole equality.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (section : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P))) ⊢
  @direct_cover_completion_silent_at K T P U R covers section
  : τ (@=
      (Hom
        (@Psh_cat K)
        (@yoneda_psh K U)
        (@DirectCoverCompletionPsh K T P))
      (@direct_cover_completion_glue K T P U R covers
        (@direct_cover_completion_restrict K T P U R section))
      section);

// Formation does not definitionally collapse to the generating presheaf.
assertnot [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K)) ⊢
  @DirectCoverCompletionPsh K T P
  ≡ P;

// Silent is propositional/internal, not a runtime glue reduction.
assertnot [K : Cat]
  (T : τ (@GrothTopology K))
  (P : τ (@Psh K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (section : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P))) ⊢
  @direct_cover_completion_glue K T P U R covers
    (@direct_cover_completion_restrict K T P U R section)
  ≡ section;
