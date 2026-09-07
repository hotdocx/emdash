/*
  Pasting and identity for the existing internal Hom factor points.

  The path helper uses only generic associativity and congruence.
  The public operations compose factor points, not a new square datatype.
*/
require open emdash.emdash3_2_hom_factor_spaces;

// Associate and substitute the two factor equations.
symbol hom_factor_paste_path
  [C : Cat]
  [A0 B0 A1 B1 A2 B2 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (d2 : τ (Hom C A2 B2))
  (a0 : τ (Hom C A0 A1))
  (a1 : τ (Hom C A1 A2))
  (b0 : τ (Hom C B0 B1))
  (b1 : τ (Hom C B1 B2))
  (p0 : τ (@= (Hom C A0 B1) (@comp_fapp0 C A0 A1 B1 d1 a0) (@comp_fapp0 C A0 B0 B1 b0 d0)))
  (p1 : τ (@= (Hom C A1 B2) (@comp_fapp0 C A1 A2 B2 d2 a1) (@comp_fapp0 C A1 B1 B2 b1 d1)))
  : τ (@= (Hom C A0 B2)
      (@comp_fapp0 C A0 A2 B2 d2 (@comp_fapp0 C A0 A1 A2 a1 a0))
      (@comp_fapp0 C A0 B0 B2 (@comp_fapp0 C B0 B1 B2 b1 b0) d0))
≔ (@eq_trans _ _ _ _
      (@comp_assoc C A0 A1 A2 B2 d2 a1 a0)
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A1 B2) (Hom C A0 B2)
        (λ h : τ (Hom C A1 B2), @comp_fapp0 C A0 A1 B2 h a0) _ _ p1)
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C A0 A1 B1 B2 b1 d1 a0))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A0 B1) (Hom C A0 B2)
        (λ h : τ (Hom C A0 B1), @comp_fapp0 C A0 B1 B2 b1 h) _ _ p0)
      (@comp_assoc C A0 B0 B1 B2 b1 b0 d0)))));

symbol hom_precomp_factor_identity
  [C : Cat]
  [A B : τ (Obj C)]
  (d : τ (Hom C A B))
  : τ (@HomPrecompFactor C A B B d (@comp_fapp0 C A A B d (@id C A)))
≔ @hom_precomp_factor_intro C A B B d (@comp_fapp0 C A A B d (@id C A))
    (@id C B) (@eq_refl (Hom C A B) d);

symbol hom_postcomp_factor_identity
  [C : Cat]
  [A B : τ (Obj C)]
  (d : τ (Hom C A B))
  : τ (@HomPostcompFactor C A B A d (@comp_fapp0 C A B B (@id C B) d))
≔ @hom_postcomp_factor_intro C A B A d (@comp_fapp0 C A B B (@id C B) d)
    (@id C A) (@eq_refl (Hom C A B) d);

// Compose precomposition factors along the two upper arrows f and g.
symbol hom_precomp_factor_paste
  [C : Cat]
  [A0 B0 A1 B1 A2 B2 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (d2 : τ (Hom C A2 B2))
  (f : τ (Hom C A0 A1))
  (g : τ (Hom C A1 A2))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g)))
  : τ (@HomPrecompFactor C A0 B0 B2 d0
      (@comp_fapp0 C A0 A2 B2 d2 (@comp_fapp0 C A0 A1 A2 g f)))
≔ @hom_precomp_factor_intro C A0 B0 B2 d0
    (@comp_fapp0 C A0 A2 B2 d2 (@comp_fapp0 C A0 A1 A2 g f))
    (@comp_fapp0 C B0 B1 B2
        (@hom_precomp_factor_arrow C A1 B1 B2 d1
          (@comp_fapp0 C A1 A2 B2 d2 g) G)
        (@hom_precomp_factor_arrow C A0 B0 B1 d0
          (@comp_fapp0 C A0 A1 B1 d1 f) F))
    (@eq_sym _ _ _
      (@hom_factor_paste_path C A0 B0 A1 B1 A2 B2 d0 d1 d2 f g
          (@hom_precomp_factor_arrow C A0 B0 B1 d0
            (@comp_fapp0 C A0 A1 B1 d1 f) F)
          (@hom_precomp_factor_arrow C A1 B1 B2 d1
            (@comp_fapp0 C A1 A2 B2 d2 g) G)
        (@eq_sym _ _ _
            (@hom_precomp_factor_path C A0 B0 B1 d0
              (@comp_fapp0 C A0 A1 B1 d1 f) F))
          (@eq_sym _ _ _
            (@hom_precomp_factor_path C A1 B1 B2 d1
              (@comp_fapp0 C A1 A2 B2 d2 g) G))));

// Compose postcomposition factors along the two lower arrows f and g.
symbol hom_postcomp_factor_paste
  [C : Cat]
  [A0 B0 A1 B1 A2 B2 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (d2 : τ (Hom C A2 B2))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B2))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1 (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A2 B2 A1 d2 (@comp_fapp0 C A1 B1 B2 g d1)))
  : τ (@HomPostcompFactor C A2 B2 A0 d2
      (@comp_fapp0 C A0 B0 B2 (@comp_fapp0 C B0 B1 B2 g f) d0))
≔ @hom_postcomp_factor_intro C A2 B2 A0 d2
    (@comp_fapp0 C A0 B0 B2 (@comp_fapp0 C B0 B1 B2 g f) d0)
    (@comp_fapp0 C A0 A1 A2
        (@hom_postcomp_factor_arrow C A2 B2 A1 d2
          (@comp_fapp0 C A1 B1 B2 g d1) G)
        (@hom_postcomp_factor_arrow C A1 B1 A0 d1
          (@comp_fapp0 C A0 B0 B1 f d0) F))
    (@hom_factor_paste_path C A0 B0 A1 B1 A2 B2 d0 d1 d2
        (@hom_postcomp_factor_arrow C A1 B1 A0 d1
          (@comp_fapp0 C A0 B0 B1 f d0) F)
        (@hom_postcomp_factor_arrow C A2 B2 A1 d2
          (@comp_fapp0 C A1 B1 B2 g d1) G) f g
        (@hom_postcomp_factor_path C A1 B1 A0 d1
          (@comp_fapp0 C A0 B0 B1 f d0) F)
        (@hom_postcomp_factor_path C A2 B2 A1 d2
          (@comp_fapp0 C A1 B1 B2 g d1) G));
