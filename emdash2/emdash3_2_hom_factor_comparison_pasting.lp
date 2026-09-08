/* Generic pasting of the original Hom factors; no diagram carrier is added. */
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_abelian_categories;

// If k a=i, i r=h=k L and k is monic, retain the original r as an a-factor of L.
symbol monic_comparison_factor
  [C : Cat]
  [A K B T : τ (Obj C)]
  (i : τ (Hom C A B))
  (k : τ (Hom C K B))
  (a : τ (Hom C A K))
  (comparison : τ (@= (Hom C A B) (@comp_fapp0 C A K B k a) i))
  (h : τ (Hom C T B))
  (original : τ (@HomPostcompFactor C K B T k h))
  (other : τ (@HomPostcompFactor C A B T i h))
  (monic : τ (@IsMonic C K B k))
  : τ (@HomPostcompFactor C A K T a (@hom_postcomp_factor_arrow C K B T k h original))
≔ @hom_postcomp_factor_intro C A K T a (@hom_postcomp_factor_arrow C K B T k h original) (@hom_postcomp_factor_arrow C A B T i h other)
    (monic T (@comp_fapp0 C T A K a (@hom_postcomp_factor_arrow C A B T i h other)) (@hom_postcomp_factor_arrow C K B T k h original)
      (@eq_trans _ _ _ _
        (@comp_assoc C T A K B k a (@hom_postcomp_factor_arrow C A B T i h other))
        (@eq_trans _ _ _ _
          (@eq_ap (Hom C A B) (Hom C T B)
            (λ f : τ (Hom C A B), @comp_fapp0 C T A B f (@hom_postcomp_factor_arrow C A B T i h other)) _ _ comparison)
          (@eq_trans _ _ _ _ (@hom_postcomp_factor_path C A B T i h other) (@eq_sym _ _ _ (@hom_postcomp_factor_path C K B T k h original))))));

// Paste cycle and quotient factors, then cancel the inverse target comparison.
symbol homology_covered_factor_paste
  [C : Cat]
  [E T K Z A H Q R : τ (Obj C)]
  (e : τ (Hom C E T))
  (delta : τ (Hom C T R))
  (pi : τ (Hom C K R))
  (a : τ (Hom C A K))
  (k : τ (Hom C Z A))
  (c : τ (Hom C A Q))
  (j : τ (Hom C H Q))
  (L : τ (Hom C E K))
  (v : τ (Hom C R Q))
  (w : τ (Hom C Q R))
  (factorA : τ (@HomPostcompFactor C A K E a L))
  (cycles : τ (@HomPostcompFactor C Z A E k (@hom_postcomp_factor_arrow C A K E a L factorA)))
  (quotient : τ (@HomPostcompFactor C H Q Z j (@comp_fapp0 C Z A Q c k)))
  (cover : τ (@= (Hom C E R) (@comp_fapp0 C E T R delta e) (@comp_fapp0 C E K R pi L)))
  (forward : τ (@= (Hom C A R) (@comp_fapp0 C A Q R w c) (@comp_fapp0 C A K R pi a)))
  (cancel : τ (@= (Hom C Q Q) (@comp_fapp0 C Q R Q v w) (@id C Q)))
  : τ (@HomPostcompFactor C H Q E j (@comp_fapp0 C E T Q (@comp_fapp0 C T R Q v delta) e))
≔ @hom_postcomp_factor_intro C H Q E j
    (@comp_fapp0 C E T Q (@comp_fapp0 C T R Q v delta) e)
    (@hom_postcomp_factor_arrow C H Q E j (@comp_fapp0 C E A Q c (@hom_postcomp_factor_arrow C A K E a L factorA)) (@hom_postcomp_factor_paste C E A Z A H Q (@hom_postcomp_factor_arrow C A K E a L factorA) k j (@id C A) c cycles quotient))
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C H Q E j (@comp_fapp0 C E A Q c (@hom_postcomp_factor_arrow C A K E a L factorA)) (@hom_postcomp_factor_paste C E A Z A H Q (@hom_postcomp_factor_arrow C A K E a L factorA) k j (@id C A) c cycles quotient))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C Q Q) (Hom C E Q)
        (λ f : τ (Hom C Q Q), @comp_fapp0 C E Q Q f (@comp_fapp0 C E A Q c (@hom_postcomp_factor_arrow C A K E a L factorA))) _ _ (@eq_sym _ _ _ cancel))
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C E Q R Q v w (@comp_fapp0 C E A Q c (@hom_postcomp_factor_arrow C A K E a L factorA))))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C E R) (Hom C E Q)
        (λ f : τ (Hom C E R), @comp_fapp0 C E R Q v f) _ _
        (@comp_assoc C E A Q R w c (@hom_postcomp_factor_arrow C A K E a L factorA)))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A R) (Hom C E Q)
        (λ f : τ (Hom C A R), @comp_fapp0 C E R Q v (@comp_fapp0 C E A R f (@hom_postcomp_factor_arrow C A K E a L factorA))) _ _ forward)
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C E R) (Hom C E Q)
        (λ f : τ (Hom C E R), @comp_fapp0 C E R Q v f) _ _
        (@eq_sym _ _ _ (@comp_assoc C E A K R pi a (@hom_postcomp_factor_arrow C A K E a L factorA))))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C E K) (Hom C E Q)
        (λ f : τ (Hom C E K), @comp_fapp0 C E R Q v (@comp_fapp0 C E K R pi f)) _ _
        (@hom_postcomp_factor_path C A K E a L factorA))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C E R) (Hom C E Q)
        (λ f : τ (Hom C E R), @comp_fapp0 C E R Q v f) _ _ (@eq_sym _ _ _ cover))
      (@comp_assoc C E T R Q v delta e)))))))));
