/* The comparison changes the factor view, not the selected arrow. */
require open emdash.emdash3_2_hom_factor_comparison_pasting;

assert
  (C : Cat)
  (A K B T : τ (Obj C))
  (i : τ (Hom C A B))
  (k : τ (Hom C K B))
  (a : τ (Hom C A K))
  (comparison : τ (@= (Hom C A B) (@comp_fapp0 C A K B k a) i))
  (h : τ (Hom C T B))
  (original : τ (@HomPostcompFactor C K B T k h))
  (other : τ (@HomPostcompFactor C A B T i h))
  (monic : τ (@IsMonic C K B k))
  ⊢ @monic_comparison_factor C A K B T i k a comparison h original other monic : τ (@HomPostcompFactor C A K T a (@hom_postcomp_factor_arrow C K B T k h original));
assert
  (C : Cat)
  (A K B T : τ (Obj C))
  (i : τ (Hom C A B))
  (k : τ (Hom C K B))
  (a : τ (Hom C A K))
  (comparison : τ (@= (Hom C A B) (@comp_fapp0 C A K B k a) i))
  (h : τ (Hom C T B))
  (original : τ (@HomPostcompFactor C K B T k h))
  (other : τ (@HomPostcompFactor C A B T i h))
  (monic : τ (@IsMonic C K B k))
  ⊢ @hom_postcomp_factor_arrow C A K T a
      (@hom_postcomp_factor_arrow C K B T k h original) (@monic_comparison_factor C A K B T i k a comparison h original other monic)
    ≡ @hom_postcomp_factor_arrow C A B T i h other;
