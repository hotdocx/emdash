/*
  Fibrewise dependent sums of directed Cat-valued families.

  Given E : K -> Cat and D : Sigma(E) -> Cat, the composite family is

    k |-> Sigma(e : E[k]), D[(k,e)].

  This stable constructor is the directed-family form of composing two
  Grothendieck fibrations.  Its whole first projection carries base action,
  naturality, and higher action internally as one displayed functor.  The
  first boundary exposes fibre, pairwise base-arrow, and projection-component
  computation.  A total-category Fubini comparison remains separately
  consumer-gated.

  The module does not add external coherence fields, a broad Sigma eta, a
  categorical pullback, a Kan extension, a topology, or sheafification.
*/

require open emdash.emdash3_2;

// Fibrewise dependent sum: k |-> Sigma(e:E[k]) D[(k,e)].
injective symbol FibrewiseSigma_catd
  [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  : τ (Catd K);

// D restricted to the canonical inclusion e |-> (k,e).
symbol fibrewise_sigma_fibre_catd
  [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  (k : τ (Obj K))
  : τ (Catd (@Fibre_cat K E k))
≔ @Pullback_catd
    (@Fibre_cat K E k)
    (@Sigma_cat K E)
    D
    (@sigma_intro_tapp0_func K E k);

// Readable dependent-sum value at k.
symbol fibrewise_sigma_value_cat
  [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  (k : τ (Obj K))
  : Cat
≔ @Sigma_cat
    (@Fibre_cat K E k)
    (@fibrewise_sigma_fibre_catd K E D k);

// Fibre beta for the composite family.
rule @fapp0 _ Cat_cat (@FibrewiseSigma_catd $K $E $D) $k
  ↪ @fibrewise_sigma_value_cat $K $E $D $k;

/*
  Pairwise base-arrow computation:

    FibrewiseSigma(E,D)[r](e,d)
      ↪ (E[r](e), D[(r,id)](d)).

  This is the constructor beta for the already-selected stable family action.
  The dependent second component is transported along the canonical Sigma
  arrow over r.  Generic Catd action continues to own higher functoriality;
  no external square or consumer-specific sieve rule is introduced.
*/
rule fapp0
      (@fapp1_fapp0
        _ Cat_cat
        (@FibrewiseSigma_catd $K $E $D)
        $x $y $r)
      (Struct_sigma $e $d)
  ↪ @Struct_sigma
      (Obj (@Fibre_cat $K $E $y))
      (λ e0 : τ (Obj (@Fibre_cat $K $E $y)),
        Obj (@Fibre_cat
          (@Fibre_cat $K $E $y)
          (@fibrewise_sigma_fibre_catd $K $E $D $y)
          e0))
      (fapp0
        (@fapp1_fapp0 $K Cat_cat $E $x $y $r)
        $e)
      (fapp0
        (@fapp1_fapp0
          (@Sigma_cat $K $E)
          Cat_cat
          $D
          (Struct_sigma $x $e)
          (Struct_sigma
            $y
            (fapp0
              (@fapp1_fapp0 $K Cat_cat $E $x $y $r)
              $e))
          (@sigma_transport_arrow $K $E $x $y $r $e))
        $d);

// Whole first projection from the fibrewise dependent sum to E.
injective symbol fibrewise_sigma_proj1_funcd
  [K : Cat]
  (E : τ (Catd K))
  (D : τ (Catd (@Sigma_cat K E)))
  : τ (Functord (@FibrewiseSigma_catd K E D) E);

// Its component at k is the ordinary Sigma first projection.
rule @tapp0_fapp0
      _ Cat_cat _ _ $k
      (@fibrewise_sigma_proj1_funcd $K $E $D)
  ↪ @Sigma_proj1_func
      (@Fibre_cat $K $E $k)
      (@fibrewise_sigma_fibre_catd $K $E $D $k);
