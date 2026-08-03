/*
  Reviewer for the direct eta/glue/silent cover-completion HIT boundary.

  Unit, matching data, and generated sections are whole presheaf maps.  The
  silent law is an internal path and deliberately does not collapse glue by
  runtime conversion.  No sheafification or reflector claim is made yet.
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

// Restriction is transparent composition with the exact sieve inclusion.
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
  ≡ @comp_fapp0
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@yoneda_psh K U)
      (@DirectCoverCompletionPsh K T P)
      section
      (@ordinary_sieve_extension_inclusion K U R);

// Silent is a first-class path at the whole section classifier.
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
  @direct_cover_completion_silent K T P U R covers section
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
