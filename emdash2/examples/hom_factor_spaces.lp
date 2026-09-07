/* Internal Hom-factor beta, identity, and target guards. */
require open emdash.emdash3_2_hom_factor_composition;

assert
  (C : Cat)
  (A B T : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C A T))
  (u : τ (Hom C B T))
  (p : τ (@= (Hom C A T) (@comp_fapp0 C A B T u f) g))
  ⊢ @hom_precomp_factor_arrow C A B T f g (@hom_precomp_factor_intro C A B T f g u p) ≡ u;

assert
  (C : Cat)
  (A B T : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C A T))
  (u : τ (Hom C B T))
  (p : τ (@= (Hom C A T) (@comp_fapp0 C A B T u f) g))
  ⊢ @hom_precomp_factor_path C A B T f g (@hom_precomp_factor_intro C A B T f g u p) ≡ p;

assertnot
  (C : Cat)
  (A B T : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C A T))
  (u : τ (Hom C B T))
  (p : τ (@= (Hom C A T) (@comp_fapp0 C A B T u f) g))
  (other : τ (Hom C A T))
  ⊢ (@hom_precomp_factor_intro C A B T f g u p) : τ (@HomPrecompFactor C A B T f other);

assert
  (C : Cat) (A B : τ (Obj C)) (d : τ (Hom C A B))
  ⊢ @hom_precomp_factor_arrow C A B B d (@comp_fapp0 C A A B d (@id C A))
      (@hom_precomp_factor_identity C A B d)
  ≡ @id C B;

assert
  (C : Cat)
  (A B T : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C T B))
  (u : τ (Hom C T A))
  (p : τ (@= (Hom C T B) (@comp_fapp0 C T A B f u) g))
  ⊢ @hom_postcomp_factor_arrow C A B T f g (@hom_postcomp_factor_intro C A B T f g u p) ≡ u;

assert
  (C : Cat)
  (A B T : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C T B))
  (u : τ (Hom C T A))
  (p : τ (@= (Hom C T B) (@comp_fapp0 C T A B f u) g))
  ⊢ @hom_postcomp_factor_path C A B T f g (@hom_postcomp_factor_intro C A B T f g u p) ≡ p;

assertnot
  (C : Cat)
  (A B T : τ (Obj C))
  (f : τ (Hom C A B))
  (g : τ (Hom C T B))
  (u : τ (Hom C T A))
  (p : τ (@= (Hom C T B) (@comp_fapp0 C T A B f u) g))
  (other : τ (Hom C T B))
  ⊢ (@hom_postcomp_factor_intro C A B T f g u p) : τ (@HomPostcompFactor C A B T f other);

assert
  (C : Cat) (A B : τ (Obj C)) (d : τ (Hom C A B))
  ⊢ @hom_postcomp_factor_arrow C A B A d (@comp_fapp0 C A B B (@id C B) d)
      (@hom_postcomp_factor_identity C A B d)
  ≡ @id C A;
