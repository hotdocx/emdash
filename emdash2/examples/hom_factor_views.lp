/* Whole factors retain their arrows and original reconstruction paths. */
require open emdash.emdash3_2_hom_factor_views;

assert (C : Cat) (A B D T : τ (Obj C))
  (f : τ (Hom C A D)) (g : τ (Hom C B D)) (h : τ (Hom C T D))
  (F : τ (@HomPostcompFactor C A D T f h))
  (G : τ (@HomPostcompFactor C B D A g f))
  ⊢ @hom_postcomp_factor_arrow C B D T g h
      (@hom_postcomp_factor_trans C A B D T f g h F G)
    ≡ @comp_fapp0 C T A B
      (@hom_postcomp_factor_arrow C B D A g f G)
      (@hom_postcomp_factor_arrow C A D T f h F);

assert (C : Cat) (A B D T : τ (Obj C))
  (f : τ (Hom C A B)) (h : τ (Hom C T B)) (g : τ (Hom C B D))
  (F : τ (@HomPostcompFactor C A B T f h))
  ⊢ @hom_postcomp_factor_arrow C A D T
      (@comp_fapp0 C A B D g f) (@comp_fapp0 C T B D g h)
      (@hom_postcomp_factor_whisker C A B D T f h g F)
    ≡ @hom_postcomp_factor_arrow C A B T f h F;

assert (C : Cat) (A B D : τ (Obj C))
  (f : τ (Hom C A B)) (g : τ (Hom C A D))
  (F : τ (@HomPrecompFactor C A B D f g))
  ⊢ @hom_postcomp_factor_arrow C B D A
      (@hom_precomp_factor_arrow C A B D f g F) g
      (@hom_precomp_factor_postcomp_view C A B D f g F)
    ≡ f;

assert (C : Cat) (A B D : τ (Obj C))
  (f : τ (Hom C A B)) (g : τ (Hom C A D))
  (F : τ (@HomPrecompFactor C A B D f g))
  ⊢ @hom_postcomp_factor_path C B D A
      (@hom_precomp_factor_arrow C A B D f g F) g
      (@hom_precomp_factor_postcomp_view C A B D f g F)
    ≡ @hom_precomp_factor_path C A B D f g F;

assertnot (C : Cat) (A B D : τ (Obj C))
  (f other : τ (Hom C A B)) (g : τ (Hom C A D))
  (F : τ (@HomPrecompFactor C A B D f g))
  ⊢ @hom_postcomp_factor_arrow C B D A
      (@hom_precomp_factor_arrow C A B D f g F) g
      (@hom_precomp_factor_postcomp_view C A B D f g F)
    ≡ other;
