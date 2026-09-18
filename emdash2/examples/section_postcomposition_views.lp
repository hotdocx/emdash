require open emdash.emdash3_2;
// catalog-area: Sigma/Pi section postcomposition

// Reassociate the actual maps while retaining both runtime section heads.
assert [K : Cat] (E M D : τ (Catd K))
  (FF : τ (@Functord K E M)) (GG : τ (@Functord K M D))
  (s : τ (Obj (@Pi_cat K E))) ⊢
  @eq_refl (Obj (@Pi_cat K D))
    (@section_postcomp_sec K M D GG (@section_postcomp_sec K E M FF s))
  : τ (@= (Obj (@Pi_cat K D))
      (@section_postcomp_sec K M D GG (@section_postcomp_sec K E M FF s))
      (@section_postcomp_sec K E D (@comp_catd_fapp0 K E M D GG FF) s));

assertnot [K : Cat] (E M D : τ (Catd K))
  (FF : τ (@Functord K E M)) (GG : τ (@Functord K M D))
  (s : τ (Obj (@Pi_cat K E))) ⊢
  @section_postcomp_sec K M D GG (@section_postcomp_sec K E M FF s)
  ≡ @section_postcomp_sec K E D (@comp_catd_fapp0 K E M D GG FF) s;

// Infer the same intermediate families from the original supplied maps.
assert [K : Cat] (E M D : τ (Catd K))
  (FF : τ (@Functord K E M)) (GG : τ (@Functord K M D))
  (s : τ (Obj (@Pi_cat K E))) ⊢
  eq_refl (section_postcomp_sec GG (section_postcomp_sec FF s))
  : τ (@= (Obj (@Pi_cat K D))
      (@section_postcomp_sec K M D GG (@section_postcomp_sec K E M FF s))
      (@section_postcomp_sec K E D (@comp_catd_fapp0 K E M D GG FF) s));

// A constant target reads these same whole sections as ordinary functors.
assert [K C : Cat] (E M : τ (Catd K))
  (FF : τ (@Functord K E M)) (GG : τ (@Functord K M (@Const_catd K C)))
  (s : τ (Obj (@Pi_cat K E))) ⊢
  @eq_refl (Functor K C)
    (@section_postcomp_sec K M (@Const_catd K C) GG (@section_postcomp_sec K E M FF s))
  : τ (@= (Functor K C)
      (@section_postcomp_sec K M (@Const_catd K C) GG (@section_postcomp_sec K E M FF s))
      (@section_postcomp_sec K E (@Const_catd K C)
        (@comp_catd_fapp0 K E M (@Const_catd K C) GG FF) s));

// An arbitrary different section is not identified by this comparison.
assertnot [K : Cat] (E M D : τ (Catd K))
  (FF : τ (@Functord K E M)) (GG : τ (@Functord K M D))
  (s t : τ (Obj (@Pi_cat K E))) ⊢
  @eq_refl (Obj (@Pi_cat K D))
    (@section_postcomp_sec K M D GG (@section_postcomp_sec K E M FF s))
  : τ (@= (Obj (@Pi_cat K D))
      (@section_postcomp_sec K M D GG (@section_postcomp_sec K E M FF s))
      (@section_postcomp_sec K E D (@comp_catd_fapp0 K E M D GG FF) t));

// Existing unit computation is retained at the stable owner.
assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (@Pi_cat K E))) ⊢
  @section_postcomp_sec K E E (@id_funcd K E) s ≡ s;
