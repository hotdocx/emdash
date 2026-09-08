/* Source-isomorphism factor transport retains its arrow and reconstruction. */
require open emdash.emdash3_2_hom_factor_source_isos;

symbol C : Cat;
symbol A : τ (Obj C);
symbol K : τ (Obj C);
symbol B : τ (Obj C);
symbol T : τ (Obj C);
symbol i : τ (Hom C A B);
symbol k : τ (Hom C K B);
symbol a : τ (@IsoEvidence C A K);
symbol comparison : τ (@= (Hom C A B)
  (@comp_fapp0 C A K B k (@iso_evidence_to C A K a)) i);
symbol h : τ (Hom C T B);
symbol point : τ (@HomPostcompFactor C K B T k h);

// The same target arrow h now factors through the compared source arrow i.
assert ⊢ @hom_postcomp_factor_source_iso C A K B T i k a comparison h point
  : τ (@HomPostcompFactor C A B T i h);

// The original factor arrow is followed by the actual inverse of a.
assert ⊢ @hom_postcomp_factor_arrow C A B T i h
    (@hom_postcomp_factor_source_iso C A K B T i k a comparison h point)
  ≡ @comp_fapp0 C T K A (@iso_evidence_from C A K a)
      (@hom_postcomp_factor_arrow C K B T k h point);

// Reconstruction uses precisely that retained composite and original target.
assert ⊢ @hom_postcomp_factor_path C A B T i h
    (@hom_postcomp_factor_source_iso C A K B T i k a comparison h point)
  : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B i
        (@comp_fapp0 C T K A (@iso_evidence_from C A K a)
          (@hom_postcomp_factor_arrow C K B T k h point))) h);

// The comparison does not authorize a factor through another arrow A → B.
symbol other_i : τ (Hom C A B);
assertnot ⊢ @hom_postcomp_factor_source_iso C A K B T i k a comparison h point
  : τ (@HomPostcompFactor C A B T other_i h);
