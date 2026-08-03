/*
  Direct cover-indexed free-completion categorical-HIT boundary.

  For a site (K,T) and one Cat-valued presheaf P, this primitive whole
  presheaf is generated in the return/cover/silent shape

    eta    : P -> X,
    glue   : (R_hat -> X) -> (y(U) -> X),
    silent : glue(x o i_R) = x.

  Here R is a covering ordinary sieve and i_R:R_hat->y(U) is the existing
  whole sieve-extension inclusion.  A matching family is therefore one whole
  presheaf map: its base-arrow action and naturality remain at generic owners.
  The silent constructor is an internal path, not a runtime glue rewrite.

  This first boundary deliberately does not yet supply the dependent/non-
  dependent eliminator, computation of glue under pullback of a cover,
  topology-locality, the whole Hom universal property, functorial assembly on
  presheaf arrows, comparison with the rigid Sheaf_cat facade, a CommRing
  lift, or left exactness.  It is consequently named direct cover completion,
  not constructed sheafification.  A directed/lax silent cell would define a
  distinct effectful completion and is not introduced without a consumer.
*/

require open emdash.emdash3_2_sieve_extensions;

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

// Recursive cover constructor from one internally compatible matching map.
constant symbol direct_cover_completion_glue
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
      (@DirectCoverCompletionPsh K T P));

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
≔ @comp_fapp0
    (@Psh_cat K)
    (@ordinary_sieve_extension_psh K U R)
    (@yoneda_psh K U)
    (@DirectCoverCompletionPsh K T P)
    section
    (@ordinary_sieve_extension_inclusion K U R);

// Silent quotient: gluing the restrictions of a section returns that section.
constant symbol direct_cover_completion_silent
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
      section);
