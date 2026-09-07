/* Generic row comparison classifiers are fibres of the actual row maps. */

require open emdash.emdash3_2_short_exact_rows;

symbol ShortExactRowSourceComparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [A K B Q : τ (Obj C)]
  (i : τ (Hom C A B))
  (row : τ (@ComputationalShortExactRow C P t PA K B Q))
  : Grpd
≔ @HFiber (@IsoEvidence C A K) (Hom C A B)
    (λ e : τ (@IsoEvidence C A K),
      @comp_fapp0 C _ _ _
        (@computational_chain_pair_dnext C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) K B Q
          (@computational_short_exact_row_pair C P t PA K B Q row))
        (@iso_evidence_to C A K e))
    i;

symbol ShortExactRowTargetComparison
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t))
  [K B Q D : τ (Obj C)]
  (p : τ (Hom C B D))
  (row : τ (@ComputationalShortExactRow C P t PA K B Q))
  : Grpd
≔ @HFiber (@IsoEvidence C Q D) (Hom C B D)
    (λ e : τ (@IsoEvidence C Q D),
      @comp_fapp0 C _ _ _ (@iso_evidence_to C Q D e)
        (@computational_chain_pair_d C (@additive_preadditive C P t
          (@preabelian_additive C P t PA)) K B Q
          (@computational_short_exact_row_pair C P t PA K B Q row)))
    p;
