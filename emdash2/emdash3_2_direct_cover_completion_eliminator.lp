/*
  Whole algebra maps and the direct-cover completion recursor.

  A map h:X->Y between direct-cover algebras preserves each cover oracle by
  one equality of whole functors.  Its path-constructor coherence compares
  two whole silent paths: whiskering source silent by h versus the route using
  glue preservation, restriction/postcomposition naturality, and target
  silent.  This keeps every action and coherence internal; no family of
  component squares is stored.

  The selected primitive recursor extends P->Y into any target cover algebra
  and retains unit beta, whole glue preservation, and whole silent coherence
  in one transparent result package.  Unit and recursive glue have narrow
  runtime betas at their exact whole-presheaf composition observers; the
  silent/path beta remains higher evidence.  This is the first eliminator
  boundary, not yet uniqueness/whole Hom universality, topology-locality of
  the completion, a sheaf object, functorial reflector, or
  SheafificationCapability.
*/

require open emdash.emdash3_2_direct_cover_completion_hit;

// Postcompose every section with one whole presheaf map.
symbol direct_cover_section_postcomp_func
  [K : Cat]
  [U : τ (Obj K)]
  [X Y : τ (@Psh K)]
  (h : τ (Hom (@Psh_cat K) X Y))
  : τ (@Functor
      (@DirectCoverSection_cat K U X)
      (@DirectCoverSection_cat K U Y))
≔ @hom_postcomp_func
    (@Psh_cat K)
    (@Psh_cat K)
    (@id_func (@Psh_cat K))
    (@yoneda_psh K U)
    X Y h;

// Postcompose every matching family with the same whole presheaf map.
symbol direct_cover_matching_postcomp_func
  [K : Cat]
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  [X Y : τ (@Psh K)]
  (h : τ (Hom (@Psh_cat K) X Y))
  : τ (@Functor
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverMatching_cat K U R Y))
≔ @hom_postcomp_func
    (@Psh_cat K)
    (@Psh_cat K)
    (@id_func (@Psh_cat K))
    (@ordinary_sieve_extension_psh K U R)
    X Y h;

/*
  Restriction commutes with postcomposition.  Both factorizations compare at
  proof time with the rigid simultaneous Hom action Hom(i_R,h).
*/
symbol direct_cover_restriction_postcomp
  [K : Cat]
  [U : τ (Obj K)]
  [R : τ (@Sieve K U)]
  [X Y : τ (@Psh K)]
  (h : τ (Hom (@Psh_cat K) X Y))
  : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R Y))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverMatching_cat K U R Y)
        (@direct_cover_matching_postcomp_func K U R X Y h)
        (@ordinary_sieve_local_precomp K U R X))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y)
        (@DirectCoverMatching_cat K U R Y)
        (@ordinary_sieve_local_precomp K U R Y)
        (@direct_cover_section_postcomp_func K U X Y h)))
≔ @eq_refl
    (Hom
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverMatching_cat K U R Y))
    (@Hom_func
      (@Psh_cat K)
      (@yoneda_psh K U)
      (@ordinary_sieve_extension_psh K U R)
      X Y
      (@ordinary_sieve_extension_inclusion K U R)
      h);

// Whole preservation square for the two selected cover oracles.
symbol DirectCoverGluePreservationAt
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : Grpd
≔ @=
    (Hom
      Cat_cat
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U Y))
    (@comp_cat_fapp0
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X)
      (@DirectCoverSection_cat K U Y)
      (@direct_cover_section_postcomp_func K U X Y h)
      (@direct_cover_algebra_glue_func K T X AX U R covers))
    (@comp_cat_fapp0
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverMatching_cat K U R Y)
      (@DirectCoverSection_cat K U Y)
      (@direct_cover_algebra_glue_func K T Y AY U R covers)
      (@direct_cover_matching_postcomp_func K U R X Y h));

// Whiskering the source silent law gives one path after postcomposition.
symbol direct_cover_map_source_silent
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  (AX : τ (@DirectCoverAlgebra K T X))
  (h : τ (Hom (@Psh_cat K) X Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U Y)
        (@comp_cat_fapp0
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverSection_cat K U X)
          (@DirectCoverSection_cat K U Y)
          (@direct_cover_section_postcomp_func K U X Y h)
          (@direct_cover_algebra_glue_func K T X AX U R covers))
        (@ordinary_sieve_local_precomp K U R X))
      (@direct_cover_section_postcomp_func K U X Y h))
≔ @eq_ap
    (Hom
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverSection_cat K U X))
    (Hom
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverSection_cat K U Y))
    (λ F : τ (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U X)),
      @comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y)
        (@direct_cover_section_postcomp_func K U X Y h)
        F)
    (@comp_cat_fapp0
      (@DirectCoverSection_cat K U X)
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U X)
      (@direct_cover_algebra_glue_func K T X AX U R covers)
      (@ordinary_sieve_local_precomp K U R X))
    (@id_func (@DirectCoverSection_cat K U X))
    (@direct_cover_algebra_silent K T X AX U R covers);

/*
  The target route first uses glue preservation, then restriction naturality,
  then the target silent law.  All three paths live between whole functors.
*/
symbol direct_cover_map_target_silent
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (preserves : τ (@DirectCoverGluePreservationAt
      K T X Y AX AY h U R covers))
  : τ (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U Y)
        (@comp_cat_fapp0
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverSection_cat K U X)
          (@DirectCoverSection_cat K U Y)
          (@direct_cover_section_postcomp_func K U X Y h)
          (@direct_cover_algebra_glue_func K T X AX U R covers))
        (@ordinary_sieve_local_precomp K U R X))
      (@direct_cover_section_postcomp_func K U X Y h))
≔ @eq_trans
    (Hom
      Cat_cat
      (@DirectCoverSection_cat K U X)
      (@DirectCoverSection_cat K U Y))
    (@comp_cat_fapp0
      (@DirectCoverSection_cat K U X)
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U Y)
      (@comp_cat_fapp0
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y)
        (@direct_cover_section_postcomp_func K U X Y h)
        (@direct_cover_algebra_glue_func K T X AX U R covers))
      (@ordinary_sieve_local_precomp K U R X))
    (@comp_cat_fapp0
      (@DirectCoverSection_cat K U X)
      (@DirectCoverMatching_cat K U R X)
      (@DirectCoverSection_cat K U Y)
      (@comp_cat_fapp0
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverMatching_cat K U R Y)
        (@DirectCoverSection_cat K U Y)
        (@direct_cover_algebra_glue_func K T Y AY U R covers)
        (@direct_cover_matching_postcomp_func K U R X Y h))
      (@ordinary_sieve_local_precomp K U R X))
    (@direct_cover_section_postcomp_func K U X Y h)
    (@eq_ap
      (Hom
        Cat_cat
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U Y))
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y))
      (λ F : τ (Hom
          Cat_cat
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverSection_cat K U Y)),
        @comp_cat_fapp0
          (@DirectCoverSection_cat K U X)
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverSection_cat K U Y)
          F
          (@ordinary_sieve_local_precomp K U R X))
      _ _
      preserves)
    (@eq_trans
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U Y)
        (@comp_cat_fapp0
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverMatching_cat K U R Y)
          (@DirectCoverSection_cat K U Y)
          (@direct_cover_algebra_glue_func K T Y AY U R covers)
          (@direct_cover_matching_postcomp_func K U R X Y h))
        (@ordinary_sieve_local_precomp K U R X))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y)
        (@DirectCoverSection_cat K U Y)
        (@comp_cat_fapp0
          (@DirectCoverSection_cat K U Y)
          (@DirectCoverMatching_cat K U R Y)
          (@DirectCoverSection_cat K U Y)
          (@direct_cover_algebra_glue_func K T Y AY U R covers)
          (@ordinary_sieve_local_precomp K U R Y))
        (@direct_cover_section_postcomp_func K U X Y h))
      (@direct_cover_section_postcomp_func K U X Y h)
      (@eq_ap
        (Hom
          Cat_cat
          (@DirectCoverSection_cat K U X)
          (@DirectCoverMatching_cat K U R Y))
        (Hom
          Cat_cat
          (@DirectCoverSection_cat K U X)
          (@DirectCoverSection_cat K U Y))
        (λ F : τ (Hom
            Cat_cat
            (@DirectCoverSection_cat K U X)
            (@DirectCoverMatching_cat K U R Y)),
          @comp_cat_fapp0
            (@DirectCoverSection_cat K U X)
            (@DirectCoverMatching_cat K U R Y)
            (@DirectCoverSection_cat K U Y)
            (@direct_cover_algebra_glue_func K T Y AY U R covers)
            F)
        _ _
        (@direct_cover_restriction_postcomp K U R X Y h))
      (@eq_ap
        (Hom
          Cat_cat
          (@DirectCoverSection_cat K U Y)
          (@DirectCoverSection_cat K U Y))
        (Hom
          Cat_cat
          (@DirectCoverSection_cat K U X)
          (@DirectCoverSection_cat K U Y))
        (λ F : τ (Hom
            Cat_cat
            (@DirectCoverSection_cat K U Y)
            (@DirectCoverSection_cat K U Y)),
          @comp_cat_fapp0
            (@DirectCoverSection_cat K U X)
            (@DirectCoverSection_cat K U Y)
            (@DirectCoverSection_cat K U Y)
            F
            (@direct_cover_section_postcomp_func K U X Y h))
        _ _
        (@direct_cover_algebra_silent K T Y AY U R covers)));

// Path-constructor beta/coherence lives one level above the two silent paths.
symbol DirectCoverSilentCoherenceAt
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (preserves : τ (@DirectCoverGluePreservationAt
      K T X Y AX AY h U R covers))
  : Grpd
≔ @=
    (@=
      (Hom
        Cat_cat
        (@DirectCoverSection_cat K U X)
        (@DirectCoverSection_cat K U Y))
      (@comp_cat_fapp0
        (@DirectCoverSection_cat K U X)
        (@DirectCoverMatching_cat K U R X)
        (@DirectCoverSection_cat K U Y)
        (@comp_cat_fapp0
          (@DirectCoverMatching_cat K U R X)
          (@DirectCoverSection_cat K U X)
          (@DirectCoverSection_cat K U Y)
          (@direct_cover_section_postcomp_func K U X Y h)
          (@direct_cover_algebra_glue_func K T X AX U R covers))
        (@ordinary_sieve_local_precomp K U R X))
      (@direct_cover_section_postcomp_func K U X Y h))
    (@direct_cover_map_source_silent K T X Y AX h U R covers)
    (@direct_cover_map_target_silent
      K T X Y AX AY h U R covers preserves);

// One-cover algebra-map data: the glue square and its silent coherence.
symbol DirectCoverAlgebraMapAt
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : Grpd
≔ `Σ_ preserves : τ (@DirectCoverGluePreservationAt
      K T X Y AX AY h U R covers),
    @DirectCoverSilentCoherenceAt
      K T X Y AX AY h U R covers preserves;

// One whole algebra morphism contains every cover square and its coherence.
symbol DirectCoverAlgebraMap
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  (AX : τ (@DirectCoverAlgebra K T X))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (h : τ (Hom (@Psh_cat K) X Y))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (@Sieve K U)
        (λ R : τ (@Sieve K U),
          @Pi_grpd
            (@groth_topology_covers K T U R)
            (λ covers : τ (@groth_topology_covers K T U R),
              @DirectCoverAlgebraMapAt
                K T X Y AX AY h U R covers)));

// Select the algebra-map package at one covering sieve.
symbol direct_cover_algebra_map_at
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  [AX : τ (@DirectCoverAlgebra K T X)]
  [AY : τ (@DirectCoverAlgebra K T Y)]
  [h : τ (Hom (@Psh_cat K) X Y)]
  (M : τ (@DirectCoverAlgebraMap K T X Y AX AY h))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@DirectCoverAlgebraMapAt K T X Y AX AY h U R covers)
≔ M U R covers;

// Whole glue-preservation projection of an algebra map at one cover.
symbol direct_cover_algebra_map_glue_preservation
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  [AX : τ (@DirectCoverAlgebra K T X)]
  [AY : τ (@DirectCoverAlgebra K T Y)]
  [h : τ (Hom (@Psh_cat K) X Y)]
  (M : τ (@DirectCoverAlgebraMap K T X Y AX AY h))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@DirectCoverGluePreservationAt
      K T X Y AX AY h U R covers)
≔ sigma_Fst
    (@direct_cover_algebra_map_at K T X Y AX AY h M U R covers);

// Silent/path-constructor coherence projection at one cover.
symbol direct_cover_algebra_map_silent_coherence
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [X Y : τ (@Psh K)]
  [AX : τ (@DirectCoverAlgebra K T X)]
  [AY : τ (@DirectCoverAlgebra K T Y)]
  [h : τ (Hom (@Psh_cat K) X Y)]
  (M : τ (@DirectCoverAlgebraMap K T X Y AX AY h))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@DirectCoverSilentCoherenceAt
      K T X Y AX AY h U R covers
      (@direct_cover_algebra_map_glue_preservation
        K T X Y AX AY h M U R covers))
≔ sigma_Snd
    (@direct_cover_algebra_map_at K T X Y AX AY h M U R covers);

// The honest recursor package extends the seed and returns an algebra map.
symbol DirectCoverCompletionRecursorData
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  : Grpd
≔ `Σ_ h : τ (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y),
   `Σ_ beta : τ (@=
      (Hom (@Psh_cat K) P Y)
      (@comp_fapp0
        (@Psh_cat K)
        P
        (@DirectCoverCompletionPsh K T P)
        Y
        h
        (@direct_cover_completion_unit K T P))
      seed),
      @DirectCoverAlgebraMap
        K T
        (@DirectCoverCompletionPsh K T P)
        Y
        (@direct_cover_completion_algebra K T P)
        AY
        h;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y)) ⊢
  @DirectCoverCompletionRecursorData K T P Y AY seed
  : Grpd;

/*
  Primitive nondependent recursor.  Unit and recursive glue compute at the
  exact generic whole-presheaf composition observers below.  Preservation of
  the whole glue functor and the silent/path constructor remain first-class
  algebra-map evidence.
*/
injective symbol direct_cover_completion_rec
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  : τ (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y);

// Runtime beta for the whole return/unit constructor.
rule @comp_fapp0
      (@Psh_cat $K) _ _ _
      (@direct_cover_completion_rec $K $T $P _ _ $seed)
      (@direct_cover_completion_unit $K $T $P)
  ↪ $seed;

/*
  Runtime recursive-glue beta at the pointwise section observer.  The input
  matching family and result are still whole presheaf maps; the primitive
  whole glue functor retains matching-arrow action and naturality.
*/
rule @comp_fapp0
      (@Psh_cat $K) _ _ _
      (@direct_cover_completion_rec $K $T $P $Y $AY $seed)
      (@fapp0
        _ _
        (@direct_cover_completion_glue_func $K $T $P $U $R $covers)
        $matching)
  ↪ @fapp0
      (@DirectCoverMatching_cat $K $U $R $Y)
      (@DirectCoverSection_cat $K $U $Y)
      (@direct_cover_algebra_glue_func $K $T $Y $AY $U $R $covers)
      (@comp_fapp0
        (@Psh_cat $K)
        (@ordinary_sieve_extension_psh $K $U $R)
        (@DirectCoverCompletionPsh $K $T $P)
        $Y
        (@direct_cover_completion_rec $K $T $P $Y $AY $seed)
        $matching);

// Transparent typed view of the runtime return/unit beta.
symbol direct_cover_completion_rec_beta_unit
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  : τ (@=
      (Hom (@Psh_cat K) P Y)
      (@comp_fapp0
        (@Psh_cat K)
        P
        (@DirectCoverCompletionPsh K T P)
        Y
        (@direct_cover_completion_rec K T P Y AY seed)
        (@direct_cover_completion_unit K T P))
      seed)
≔ @eq_refl (Hom (@Psh_cat K) P Y) seed;

// Primitive whole algebra-map and silent/path-coherence evidence.
constant symbol direct_cover_completion_rec_algebra_map
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  : τ (@DirectCoverAlgebraMap
      K T
      (@DirectCoverCompletionPsh K T P)
      Y
      (@direct_cover_completion_algebra K T P)
      AY
      (@direct_cover_completion_rec K T P Y AY seed));

// Transparent package of the recursor, runtime unit beta, and algebra map.
symbol direct_cover_completion_recursor_data
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  : τ (@DirectCoverCompletionRecursorData K T P Y AY seed)
≔ @Struct_sigma
    (Hom
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y)
    (λ h : τ (Hom
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y),
      `Σ_ beta : τ (@=
          (Hom (@Psh_cat K) P Y)
          (@comp_fapp0
            (@Psh_cat K)
            P
            (@DirectCoverCompletionPsh K T P)
            Y
            h
            (@direct_cover_completion_unit K T P))
          seed),
        @DirectCoverAlgebraMap
          K T
          (@DirectCoverCompletionPsh K T P)
          Y
          (@direct_cover_completion_algebra K T P)
          AY
          h)
    (@direct_cover_completion_rec K T P Y AY seed)
    (@Struct_sigma
      (@=
        (Hom (@Psh_cat K) P Y)
        (@comp_fapp0
          (@Psh_cat K)
          P
          (@DirectCoverCompletionPsh K T P)
          Y
          (@direct_cover_completion_rec K T P Y AY seed)
          (@direct_cover_completion_unit K T P))
        seed)
      (λ _ : τ (@=
          (Hom (@Psh_cat K) P Y)
          (@comp_fapp0
            (@Psh_cat K)
            P
            (@DirectCoverCompletionPsh K T P)
            Y
            (@direct_cover_completion_rec K T P Y AY seed)
            (@direct_cover_completion_unit K T P))
          seed),
        @DirectCoverAlgebraMap
          K T
          (@DirectCoverCompletionPsh K T P)
          Y
          (@direct_cover_completion_algebra K T P)
          AY
          (@direct_cover_completion_rec K T P Y AY seed))
      (@direct_cover_completion_rec_beta_unit K T P Y AY seed)
      (@direct_cover_completion_rec_algebra_map K T P Y AY seed));

// Transparent pointwise view of the runtime recursive-glue beta.
symbol direct_cover_completion_rec_beta_glue_at
  [K : Cat]
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
      (@DirectCoverCompletionPsh K T P)))
  : τ (@=
      (Hom (@Psh_cat K) (@yoneda_psh K U) Y)
      (@comp_fapp0
        (@Psh_cat K)
        (@yoneda_psh K U)
        (@DirectCoverCompletionPsh K T P)
        Y
        (@direct_cover_completion_rec K T P Y AY seed)
        (@direct_cover_completion_glue K T P U R covers matching))
      (@fapp0
        (@DirectCoverMatching_cat K U R Y)
        (@DirectCoverSection_cat K U Y)
        (@direct_cover_algebra_glue_func K T Y AY U R covers)
        (@comp_fapp0
          (@Psh_cat K)
          (@ordinary_sieve_extension_psh K U R)
          (@DirectCoverCompletionPsh K T P)
          Y
          (@direct_cover_completion_rec K T P Y AY seed)
          matching)))
≔ @eq_refl
    (Hom (@Psh_cat K) (@yoneda_psh K U) Y)
    (@fapp0
      (@DirectCoverMatching_cat K U R Y)
      (@DirectCoverSection_cat K U Y)
      (@direct_cover_algebra_glue_func K T Y AY U R covers)
      (@comp_fapp0
        (@Psh_cat K)
        (@ordinary_sieve_extension_psh K U R)
        (@DirectCoverCompletionPsh K T P)
        Y
        (@direct_cover_completion_rec K T P Y AY seed)
        matching));

// Whole glue-preservation evidence at one cover.
symbol direct_cover_completion_rec_beta_glue
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@DirectCoverGluePreservationAt
      K T
      (@DirectCoverCompletionPsh K T P)
      Y
      (@direct_cover_completion_algebra K T P)
      AY
      (@direct_cover_completion_rec K T P Y AY seed)
      U R covers)
≔ @direct_cover_algebra_map_glue_preservation
    K T
    (@DirectCoverCompletionPsh K T P)
    Y
    (@direct_cover_completion_algebra K T P)
    AY
    (@direct_cover_completion_rec K T P Y AY seed)
    (@direct_cover_completion_rec_algebra_map K T P Y AY seed)
    U R covers;

// Higher beta/coherence for the recursive silent path constructor.
symbol direct_cover_completion_rec_beta_silent
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  : τ (@DirectCoverSilentCoherenceAt
      K T
      (@DirectCoverCompletionPsh K T P)
      Y
      (@direct_cover_completion_algebra K T P)
      AY
      (@direct_cover_completion_rec K T P Y AY seed)
      U R covers
      (@direct_cover_completion_rec_beta_glue
        K T P Y AY seed U R covers))
≔ @direct_cover_algebra_map_silent_coherence
    K T
    (@DirectCoverCompletionPsh K T P)
    Y
    (@direct_cover_completion_algebra K T P)
    AY
    (@direct_cover_completion_rec K T P Y AY seed)
    (@direct_cover_completion_rec_algebra_map K T P Y AY seed)
    U R covers;

/*
  A topology-local target supplies the required direct-cover algebra through
  the existing forgetful construction.  This is only a recursor convenience;
  it does not prove that the completion itself is topology-local.
*/
symbol direct_cover_completion_local_recursor_data
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T Y))
  (seed : τ (Hom (@Psh_cat K) P Y))
  : τ (@DirectCoverCompletionRecursorData
      K T P Y
      (@topology_local_direct_cover_algebra K T Y local)
      seed)
≔ @direct_cover_completion_recursor_data
    K T P Y (@topology_local_direct_cover_algebra K T Y local) seed;
