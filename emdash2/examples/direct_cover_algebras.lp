/*
  Reviewer for whole direct-cover oracle algebras.

  The oracle is a functor on matching hom-categories and silent is one whole
  equality.  Full topology-locality forgets to this structure by its selected
  left inverse; no converse or second inverse law is asserted here.
*/

require open emdash.emdash3_2_direct_cover_algebras;

assert [K : Cat]
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (X : τ (@Psh K)) ⊢
  @DirectCoverAt K U R X
  : Grpd;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K)) ⊢
  @DirectCoverAlgebra K T X
  : Grpd;

// A selected oracle includes its whole action between matching families.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (A : τ (@DirectCoverAlgebra K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_glue_func K T X A U R covers
  : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X));

// Silent is one whole endofunctor equality, not a component field.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (A : τ (@DirectCoverAlgebra K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_silent K T X A U R covers
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
        (@direct_cover_algebra_glue_func K T X A U R covers)
        (@ordinary_sieve_local_precomp K U R X))
      (@id Cat_cat (@DirectCoverSection_cat K U X)));

// Full restriction equivalence canonically selects the direct-cover algebra.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T X)) ⊢
  @topology_local_direct_cover_algebra K T X local
  : τ (@DirectCoverAlgebra K T X);

// Its glue projection is exactly the selected left inverse of restriction.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_glue_func
    K T X (@topology_local_direct_cover_algebra K T X local)
    U R covers
  ≡ @omega_equiv_along_left_inv
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverMatching_cat K U R X)
      (@ordinary_sieve_local_precomp K U R X)
      (local U R covers);

// Its silent projection is exactly the selected whole left law.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T X))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_silent
    K T X (@topology_local_direct_cover_algebra K T X local)
    U R covers
  ≡ @omega_equiv_along_left_law
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverMatching_cat K U R X)
      (@ordinary_sieve_local_precomp K U R X)
      (local U R covers);

// The oracle view is not definitionally promoted to full topology-locality.
assertnot [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K)) ⊢
  @DirectCoverAlgebra K T X
  ≡ @IsTopologyLocalPsh K T X;
