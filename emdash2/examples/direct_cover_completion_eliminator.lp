/*
  Reviewer for the whole direct-cover completion recursor boundary.

  An algebra map preserves every whole glue functor and carries the higher
  coherence between source and target silent paths.  The primitive recursor
  extends a seed map; unit and recursive glue compute at narrow generic
  observers, while whole glue preservation and silent beta remain internal
  evidence.  No topology-locality or sheafification theorem is claimed.
*/

require open emdash.emdash3_2_direct_cover_completion_eliminator;

// One-cover map data retains both the whole glue square and silent coherence.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X Y : τ (@Psh K))
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @DirectCoverAlgebraMapAt K T X Y AX AY h U R covers
  : Grpd;

// A whole algebra map supplies that package at every covering sieve.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X Y : τ (@Psh K))
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y)) ⊢
  @DirectCoverAlgebraMap K T X Y AX AY h
  : Grpd;

// The glue-preservation projection is exactly the first Sigma component.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X Y : τ (@Psh K))
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (M : τ (@DirectCoverAlgebraMap K T X Y AX AY h))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_map_glue_preservation
    K T X Y AX AY h M U R covers
  ≡ sigma_Fst (M U R covers);

// The second component is coherence between the two whole silent routes.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X Y : τ (@Psh K))
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (M : τ (@DirectCoverAlgebraMap K T X Y AX AY h))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_algebra_map_silent_coherence
    K T X Y AX AY h M U R covers
  ≡ sigma_Snd (M U R covers);

// The primitive recursor result contains an extension and all three laws.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @direct_cover_completion_recursor_data K T P Y AY seed
  : τ (@DirectCoverCompletionRecursorData K T P Y AY seed);

// Its selected extension is one whole presheaf map.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @direct_cover_completion_rec K T P Y AY seed
  : τ (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y);

// Unit beta is a first-class path between whole presheaf maps.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @direct_cover_completion_rec_beta_unit K T P Y AY seed
  : τ (@=
      (Hom (@Psh_cat K) P Y)
      (@comp_fapp0
        (@Psh_cat K)
        P
        (@DirectCoverCompletionPsh K T P)
        Y
        (@direct_cover_completion_rec K T P Y AY seed)
        (@direct_cover_completion_unit K T P))
      seed);

// Glue beta is one whole functor square, not component equations.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_completion_rec_beta_glue
    K T P Y AY seed U R covers
  : τ (@DirectCoverGluePreservationAt
      K T
      (@DirectCoverCompletionPsh K T P)
      Y
      (@direct_cover_completion_algebra K T P)
      AY
      (@direct_cover_completion_rec K T P Y AY seed)
      U R covers);

// Silent beta is higher coherence between the two whole functor paths.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R)) ⊢
  @direct_cover_completion_rec_beta_silent
    K T P Y AY seed U R covers
  : τ (@DirectCoverSilentCoherenceAt
      K T
      (@DirectCoverCompletionPsh K T P)
      Y
      (@direct_cover_completion_algebra K T P)
      AY
      (@direct_cover_completion_rec K T P Y AY seed)
      U R covers
      (@direct_cover_completion_rec_beta_glue
        K T P Y AY seed U R covers));

// An internal direct-cover sheaf target enters without restating its fields.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (sheaf : τ (@DirectCoverSheafStructure K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @direct_cover_completion_sheaf_recursor_data K T P Y sheaf seed
  : τ (@DirectCoverCompletionRecursorData
      K T P Y
      (@direct_cover_sheaf_structure_algebra K T Y sheaf)
      seed);

// A topology-local target supplies the target algebra without extra fields.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @direct_cover_completion_local_recursor_data K T P Y local seed
  : τ (@DirectCoverCompletionRecursorData
      K T P Y
      (@topology_local_direct_cover_algebra K T Y local)
      seed);

// The return/unit constructor computes at whole-presheaf composition.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @comp_fapp0
    (@Psh_cat K)
    P
    (@DirectCoverCompletionPsh K T P)
    Y
    (@direct_cover_completion_rec K T P Y AY seed)
    (@direct_cover_completion_unit K T P)
  ≡ seed;

// Recursive glue computes pointwise while all inputs remain whole maps.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (matching : τ (Hom
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@DirectCoverCompletionPsh K T P))) ⊢
  @comp_fapp0
    (@Psh_cat K)
    (@yoneda_psh K U)
    (@DirectCoverCompletionPsh K T P)
    Y
    (@direct_cover_completion_rec K T P Y AY seed)
    (@direct_cover_completion_glue K T P U R covers matching)
  ≡ @fapp0
      (@DirectCoverMatching_cat K U R Y)
      (@DirectCoverSection_cat K U Y)
      (@direct_cover_algebra_glue_func K T Y AY U R covers)
      (@comp_fapp0
        (@Psh_cat K)
        (@ordinary_sieve_extension_psh K U R)
        (@DirectCoverCompletionPsh K T P)
        Y
        (@direct_cover_completion_rec K T P Y AY seed)
        matching);
