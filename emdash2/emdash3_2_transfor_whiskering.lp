/* Whole whiskering through the original composition functors.
   Definitions only: transformations and selected inverse data are retained. */

require open emdash.emdash3_2;

// Precompose both selected maps and their laws by H.
symbol iso_evidence_prewhisker [A B C : Cat] (H : τ (Functor A B))
 (F G : τ (Functor B C)) (i : τ (IsoEvidence (Functor_cat B C) F G))
 : τ (IsoEvidence (Functor_cat A C) (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H))
≔ @iso_evidence_fmap (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C H) F G i;

// Postcompose both selected maps and their laws by H.
symbol iso_evidence_postwhisker [A B C : Cat] (H : τ (Functor B C))
 (F G : τ (Functor A B)) (i : τ (IsoEvidence (Functor_cat A B) F G))
 : τ (IsoEvidence (Functor_cat A C) (@comp_cat_fapp0 A B C H F) (@comp_cat_fapp0 A B C H G))
≔ @iso_evidence_fmap (Functor_cat A B) (Functor_cat A C) (@comp_cat_cov_func A B C H) F G i;

// The whole transformation t whiskered on the source by H.
symbol transf_prewhisker [A B C : Cat] (H : τ (Functor A B))
 (F G : τ (Functor B C)) (t : τ (@Transf B C F G))
 : τ (@Transf A C (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H))
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func A B C H F G) t;

// The whole transformation t whiskered on the target by H.
symbol transf_postwhisker [A B C : Cat] (H : τ (Functor B C))
 (F G : τ (Functor A B)) (t : τ (@Transf A B F G))
 : τ (@Transf A C (@comp_cat_fapp0 A B C H F) (@comp_cat_fapp0 A B C H G))
≔ @fapp0 _ _ (@comp_cat_cov_fapp1_func A B C H F G) t;
