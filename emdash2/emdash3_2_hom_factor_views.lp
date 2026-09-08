/* Transparent views/compositions of existing whole Hom factors. */
require open emdash.emdash3_2_hom_factor_composition;

// Chain two factors ending at the same object, retaining their composite arrow.
symbol hom_postcomp_factor_trans
  [C : Cat] [A B D T : τ (Obj C)]
  (f : τ (Hom C A D)) (g : τ (Hom C B D)) (h : τ (Hom C T D))
  (F : τ (@HomPostcompFactor C A D T f h))
  (G : τ (@HomPostcompFactor C B D A g f))
  : τ (@HomPostcompFactor C B D T g h)
≔ @hom_postcomp_factor_paste C T D A D B D h f g
    (@id C D) (@id C D) F G;

// Postcompose both sides of a factorization; its factor arrow is unchanged.
symbol hom_postcomp_factor_whisker
  [C : Cat] [A B D T : τ (Obj C)]
  (f : τ (Hom C A B)) (h : τ (Hom C T B)) (g : τ (Hom C B D))
  (F : τ (@HomPostcompFactor C A B T f h))
  : τ (@HomPostcompFactor C A D T
      (@comp_fapp0 C A B D g f) (@comp_fapp0 C T B D g h))
≔ @hom_postcomp_factor_paste C T B A B A D h f
    (@comp_fapp0 C A B D g f) (@id C B) g F
    (@hom_postcomp_factor_identity C A D (@comp_fapp0 C A B D g f));

// Read the same triangle from its other leg, using its original reconstruction.
symbol hom_precomp_factor_postcomp_view
  [C : Cat] [A B D : τ (Obj C)]
  (f : τ (Hom C A B)) (g : τ (Hom C A D))
  (F : τ (@HomPrecompFactor C A B D f g))
  : τ (@HomPostcompFactor C B D A
      (@hom_precomp_factor_arrow C A B D f g F) g)
≔ @hom_postcomp_factor_intro C B D A
    (@hom_precomp_factor_arrow C A B D f g F) g f
    (@hom_precomp_factor_path C A B D f g F);
