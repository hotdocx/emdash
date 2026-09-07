/*
  Ordinary internal Hom factor spaces for post- and precomposition.

  These are transparent instances of HFiber, not new square constructors.
  A composite target can display a square; the stored data remain a triangle
  in the existing Hom family.
*/
require open emdash.emdash3_2;

// Postcomposition factors: f ∘ u = g.
symbol HomPostcompFactor
  [C : Cat]
  [A B T : τ (Obj C)]
  (f : τ (Hom C A B))
  (g : τ (Hom C T B))
  : Grpd
≔ @HFiber (Hom C T A) (Hom C T B)
    (λ u : τ (Hom C T A), @comp_fapp0 C T A B f u) g;

// Assemble the existing postcomposition fibre point.
symbol hom_postcomp_factor_intro
  [C : Cat]
  [A B T : τ (Obj C)]
  [f : τ (Hom C A B)]
  [g : τ (Hom C T B)]
  (u : τ (Hom C T A))
  (path : τ (@= (Hom C T B) (@comp_fapp0 C T A B f u) g))
  : τ (@HomPostcompFactor C A B T f g)
≔ @Struct_sigma (Hom C T A)
    (λ v : τ (Hom C T A), @= (Hom C T B) (@comp_fapp0 C T A B f v) g)
    u path;

// The retained postcomposition factor arrow.
symbol hom_postcomp_factor_arrow
  [C : Cat]
  [A B T : τ (Obj C)]
  [f : τ (Hom C A B)]
  [g : τ (Hom C T B)]
  (point : τ (@HomPostcompFactor C A B T f g))
  : τ (Hom C T A)
≔ @hfiber_point (Hom C T A) (Hom C T B)
    (λ u : τ (Hom C T A), @comp_fapp0 C T A B f u) g point;

// The retained postcomposition reconstruction.
symbol hom_postcomp_factor_path
  [C : Cat]
  [A B T : τ (Obj C)]
  [f : τ (Hom C A B)]
  [g : τ (Hom C T B)]
  (point : τ (@HomPostcompFactor C A B T f g))
  : τ (@= (Hom C T B)
      (@comp_fapp0 C T A B f (@hom_postcomp_factor_arrow C A B T f g point)) g)
≔ @hfiber_path (Hom C T A) (Hom C T B)
    (λ u : τ (Hom C T A), @comp_fapp0 C T A B f u) g point;

// Precomposition factors: u ∘ f = g.
symbol HomPrecompFactor
  [C : Cat]
  [A B T : τ (Obj C)]
  (f : τ (Hom C A B))
  (g : τ (Hom C A T))
  : Grpd
≔ @HFiber (Hom C B T) (Hom C A T)
    (λ u : τ (Hom C B T), @comp_fapp0 C A B T u f) g;

// Assemble the existing precomposition fibre point.
symbol hom_precomp_factor_intro
  [C : Cat]
  [A B T : τ (Obj C)]
  [f : τ (Hom C A B)]
  [g : τ (Hom C A T)]
  (u : τ (Hom C B T))
  (path : τ (@= (Hom C A T) (@comp_fapp0 C A B T u f) g))
  : τ (@HomPrecompFactor C A B T f g)
≔ @Struct_sigma (Hom C B T)
    (λ v : τ (Hom C B T), @= (Hom C A T) (@comp_fapp0 C A B T v f) g)
    u path;

// The retained precomposition factor arrow.
symbol hom_precomp_factor_arrow
  [C : Cat]
  [A B T : τ (Obj C)]
  [f : τ (Hom C A B)]
  [g : τ (Hom C A T)]
  (point : τ (@HomPrecompFactor C A B T f g))
  : τ (Hom C B T)
≔ @hfiber_point (Hom C B T) (Hom C A T)
    (λ u : τ (Hom C B T), @comp_fapp0 C A B T u f) g point;

// The retained precomposition reconstruction.
symbol hom_precomp_factor_path
  [C : Cat]
  [A B T : τ (Obj C)]
  [f : τ (Hom C A B)]
  [g : τ (Hom C A T)]
  (point : τ (@HomPrecompFactor C A B T f g))
  : τ (@= (Hom C A T)
      (@comp_fapp0 C A B T (@hom_precomp_factor_arrow C A B T f g point) f) g)
≔ @hfiber_path (Hom C B T) (Hom C A T)
    (λ u : τ (Hom C B T), @comp_fapp0 C A B T u f) g point;
