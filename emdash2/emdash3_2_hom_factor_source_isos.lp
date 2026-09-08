/*
  Transport an existing postcomposition factor through a source isomorphism.

  If k ∘ a = i and k ∘ u = h, retain a⁻¹ ∘ u with i ∘ (a⁻¹ ∘ u) = h.
  The result is the existing internal Hom fibre, with its original target.
*/
require open emdash.emdash3_2_hom_factor_spaces;

// Reindex a postcomposition factor along the supplied source isomorphism.
symbol hom_postcomp_factor_source_iso
  [C : Cat]
  [A K B T : τ (Obj C)]
  (i : τ (Hom C A B))
  (k : τ (Hom C K B))
  (a : τ (@IsoEvidence C A K))
  (comparison : τ (@= (Hom C A B)
    (@comp_fapp0 C A K B k (@iso_evidence_to C A K a)) i))
  (h : τ (Hom C T B))
  (point : τ (@HomPostcompFactor C K B T k h))
  : τ (@HomPostcompFactor C A B T i h)
≔ @hom_postcomp_factor_intro C A B T i h
    (@comp_fapp0 C T K A (@iso_evidence_from C A K a)
      (@hom_postcomp_factor_arrow C K B T k h point))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C A B) (Hom C T B)
        (λ f : τ (Hom C A B), @comp_fapp0 C T A B f
          (@comp_fapp0 C T K A (@iso_evidence_from C A K a)
            (@hom_postcomp_factor_arrow C K B T k h point)))
        _ _ (@eq_sym _ _ _ comparison))
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _ (@comp_assoc C T A K B k
          (@iso_evidence_to C A K a)
          (@comp_fapp0 C T K A (@iso_evidence_from C A K a)
            (@hom_postcomp_factor_arrow C K B T k h point))))
        (@eq_trans _ _ _ _
          (@eq_ap (Hom C T K) (Hom C T B)
            (λ f : τ (Hom C T K), @comp_fapp0 C T K B k f)
            _ _
            (@eq_trans _ _ _ _
              (@comp_assoc C T K A K
                (@iso_evidence_to C A K a) (@iso_evidence_from C A K a)
                (@hom_postcomp_factor_arrow C K B T k h point))
              (@eq_ap (Hom C K K) (Hom C T K)
                (λ f : τ (Hom C K K), @comp_fapp0 C T K K f
                  (@hom_postcomp_factor_arrow C K B T k h point))
                _ _ (@iso_evidence_right C A K a))))
          (@hom_postcomp_factor_path C K B T k h point))));
