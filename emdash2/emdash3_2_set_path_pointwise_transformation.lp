/*
  Whole pointwise transformations into the path category of a set.

  For F,G : C -> Path(S), a pointwise family p(x) : F[x] = G[x]
  determines one whole transformation when S is a set. Naturality and every
  higher coherence lie in proposition-valued path spaces, so consumers supply
  no commuting square or coherence tower.

  `Transf` is a primitive classifier rather than an exposed record
  constructor. This module therefore owns the assembly as one stable whole
  operation and exposes only its constructor-visible component beta. Generic
  transformation action, identity, composition, and higher component action
  remain owned by the existing `tapp*`/`fapp*` calculus.
*/

require open emdash.emdash3_2;

// Pointwise path data between two functors landing in Path(S).
symbol SetPathPointwiseData
  [C : Cat]
  [S : Grpd]
  (F G : τ (@Functor C (Path_cat S)))
  : Grpd
≔ @Pi_grpd
    (Obj C)
    (λ x : τ (Obj C),
      @= S
        (@fapp0 C (Path_cat S) F x)
        (@fapp0 C (Path_cat S) G x));

// Stable whole transformation assembled from pointwise paths into a set.
injective symbol set_path_pointwise_transf
  [C : Cat]
  [S : Grpd]
  (S_set : τ (IsSetGrpd S))
  [F G : τ (@Functor C (Path_cat S))]
  (p : τ (@SetPathPointwiseData C S F G))
  : τ (@Transf C (Path_cat S) F G);

// The whole transformation exposes the selected pointwise path at each point.
rule @tapp0_fapp0 _ _ _ _ $x
      (@set_path_pointwise_transf _ _ _ _ _ $p)
  ↪ $p $x;
