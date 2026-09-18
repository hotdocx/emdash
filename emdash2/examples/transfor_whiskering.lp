require open emdash.emdash3_2_transfor_whiskering;
// catalog-area: Whole transformation and isomorphism whiskering

// The original whole transformation supplies both component actions.
assert [A B C : Cat] (H : τ (Functor A B)) (F G : τ (Functor B C))
 (t : τ (@Transf B C F G)) (a : τ (Obj A)) ⊢
 @tapp0_fapp0 A C (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H) a
   (@transf_prewhisker A B C H F G t)
 ≡ @tapp0_fapp0 B C F G (@fapp0 A B H a) t;

assert [A B C : Cat] (H : τ (Functor B C)) (F G : τ (Functor A B))
 (t : τ (@Transf A B F G)) (a : τ (Obj A)) ⊢
 @tapp0_fapp0 A C (@comp_cat_fapp0 A B C H F) (@comp_cat_fapp0 A B C H G) a
   (@transf_postwhisker A B C H F G t)
 ≡ @fapp1_fapp0 B C H (@fapp0 A B F a) (@fapp0 A B G a) (@tapp0_fapp0 A B F G a t);

// Both selected arrows survive whole precomposition.
assert [A B C : Cat] (H : τ (Functor A B)) (F G : τ (Functor B C))
 (i : τ (IsoEvidence (Functor_cat B C) F G)) ⊢
 @iso_evidence_to (Functor_cat A C) (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H)
   (@iso_evidence_prewhisker A B C H F G i)
 ≡ @transf_prewhisker A B C H F G (@iso_evidence_to (Functor_cat B C) F G i);
assert [A B C : Cat] (H : τ (Functor A B)) (F G : τ (Functor B C))
 (i : τ (IsoEvidence (Functor_cat B C) F G)) ⊢
 @iso_evidence_from (Functor_cat A C) (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H)
   (@iso_evidence_prewhisker A B C H F G i)
 ≡ @transf_prewhisker A B C H G F (@iso_evidence_from (Functor_cat B C) F G i);

// Both selected arrows survive whole postcomposition.
assert [A B C : Cat] (H : τ (Functor B C)) (F G : τ (Functor A B))
 (i : τ (IsoEvidence (Functor_cat A B) F G)) ⊢
 @iso_evidence_to (Functor_cat A C) (@comp_cat_fapp0 A B C H F) (@comp_cat_fapp0 A B C H G)
   (@iso_evidence_postwhisker A B C H F G i)
 ≡ @transf_postwhisker A B C H F G (@iso_evidence_to (Functor_cat A B) F G i);
assert [A B C : Cat] (H : τ (Functor B C)) (F G : τ (Functor A B))
 (i : τ (IsoEvidence (Functor_cat A B) F G)) ⊢
 @iso_evidence_from (Functor_cat A C) (@comp_cat_fapp0 A B C H F) (@comp_cat_fapp0 A B C H G)
   (@iso_evidence_postwhisker A B C H F G i)
 ≡ @transf_postwhisker A B C H G F (@iso_evidence_from (Functor_cat A B) F G i);
