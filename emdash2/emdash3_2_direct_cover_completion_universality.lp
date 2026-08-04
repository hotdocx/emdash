/*
  Whole Hom universality of direct cover completion.

  For one fixed target algebra, the primitive completion recursor varies as
  one whole functor in its seed map.  Its whole unit beta is the functorial
  form of the existing runtime constructor beta.  At a topology-local target,
  the categorical-HIT eta/uniqueness law says that recursion after restriction
  along the unit is the identity on the complete Hom category.  Together they
  exhibit unit precomposition as an `OmegaEquivAlong Cat_cat`.

  The eta law is deliberately scoped to topology-local targets.  It does not
  claim that an arbitrary underlying map preserves an independently selected
  one-sided cover algebra.  Both whole laws are equality evidence, not runtime
  rewrites; ordinary arrow action and naturality remain owned by the two whole
  functors.
*/

require open emdash.emdash3_2_direct_cover_completion_eliminator;
require open emdash.emdash3_2_direct_cover_completion_locality;

// Whole restriction along the direct-completion unit.
symbol direct_cover_completion_unit_precomp_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  : τ (@Functor
      (Hom_cat
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y)
      (Hom_cat (@Psh_cat K) P Y))
≔ @hom_precomp_along_func
    (@Psh_cat K)
    (@Psh_cat K)
    (@id_func (@Psh_cat K))
    Y
    P
    (@DirectCoverCompletionPsh K T P)
    (@direct_cover_completion_unit K T P);

// The primitive recursor varies functorially in its whole seed map.
injective symbol direct_cover_completion_rec_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  : τ (@Functor
      (Hom_cat (@Psh_cat K) P Y)
      (Hom_cat
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y));

// Object beta: the functorial recursor selects the deployed recursor.
rule @fapp0 _ _
      (@direct_cover_completion_rec_func $K $T $P $Y $AY)
      $seed
  ↪ @direct_cover_completion_rec $K $T $P $Y $AY $seed;

// Whole categorical-HIT beta for restriction after recursion.
constant symbol direct_cover_completion_rec_beta_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (AY : τ (@DirectCoverAlgebra K T Y))
  : τ (@=
      (Hom
        Cat_cat
        (Hom_cat (@Psh_cat K) P Y)
        (Hom_cat (@Psh_cat K) P Y))
      (@comp_cat_fapp0
        (Hom_cat (@Psh_cat K) P Y)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (Hom_cat (@Psh_cat K) P Y)
        (@direct_cover_completion_unit_precomp_func K T P Y)
        (@direct_cover_completion_rec_func K T P Y AY))
      (@id Cat_cat (Hom_cat (@Psh_cat K) P Y)));

/*
  Whole categorical-HIT eta/uniqueness at a topology-local target:

    rec_local o precomp_unit = id.

  Locality selects the canonical target algebra.  This is the primitive
  uniqueness clause of the categorical eliminator, not a consequence claimed
  for arbitrary independently selected cover algebras.
*/
constant symbol direct_cover_completion_rec_eta_local_func
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T Y))
  : τ (@=
      (Hom
        Cat_cat
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y))
      (@comp_cat_fapp0
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (Hom_cat (@Psh_cat K) P Y)
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)
        (@direct_cover_completion_rec_func
          K T P Y (@topology_local_direct_cover_algebra K T Y local))
        (@direct_cover_completion_unit_precomp_func K T P Y))
      (@id Cat_cat
        (Hom_cat
          (@Psh_cat K)
          (@DirectCoverCompletionPsh K T P)
          Y)));

// Whole universal property into a topology-local target.
symbol direct_cover_completion_hom_omega
  [K : Cat]
  (T : τ (@GrothTopology K))
  (P Y : τ (@Psh K))
  (local : τ (@IsTopologyLocalPsh K T Y))
  : τ (@OmegaEquivAlong
      Cat_cat
      (Hom_cat
        (@Psh_cat K)
        (@DirectCoverCompletionPsh K T P)
        Y)
      (Hom_cat (@Psh_cat K) P Y)
      (@direct_cover_completion_unit_precomp_func K T P Y))
≔ @omega_equiv_along_intro
    Cat_cat
    (Hom_cat
      (@Psh_cat K)
      (@DirectCoverCompletionPsh K T P)
      Y)
    (Hom_cat (@Psh_cat K) P Y)
    (@direct_cover_completion_unit_precomp_func K T P Y)
    (@direct_cover_completion_rec_func
      K T P Y (@topology_local_direct_cover_algebra K T Y local))
    (@direct_cover_completion_rec_func
      K T P Y (@topology_local_direct_cover_algebra K T Y local))
    (@direct_cover_completion_rec_eta_local_func K T P Y local)
    (@direct_cover_completion_rec_beta_func
      K T P Y (@topology_local_direct_cover_algebra K T Y local));
