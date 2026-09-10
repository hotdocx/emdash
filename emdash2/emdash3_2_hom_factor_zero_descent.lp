/*
  Zero composites through existing Hom factors.
  Monic pasting and epic descent share the existing generic composition,
  cancellation and factor owners. These are defined proofs, not new rules.
*/
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;
require open emdash.emdash3_2_hom_factor_views;

// Dual to hom_precomp_factor_paste_zero_path: cancel the final monomorphism.
symbol hom_postcomp_factor_paste_zero_path
  [C : Cat] (S : τ (@PreadditiveCategory C))
  [A0 B0 A1 B1 A2 B2 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0))
  (d1 : τ (Hom C A1 B1))
  (d2 : τ (Hom C A2 B2))
  (f : τ (Hom C B0 B1))
  (g : τ (Hom C B1 B2))
  (F : τ (@HomPostcompFactor C A1 B1 A0 d1
    (@comp_fapp0 C A0 B0 B1 f d0)))
  (G : τ (@HomPostcompFactor C A2 B2 A1 d2
    (@comp_fapp0 C A1 B1 B2 g d1)))
  (monic : τ (@IsMonic C A2 B2 d2))
  (zero : τ (@= (Hom C B0 B2)
    (@comp_fapp0 C B0 B1 B2 g f) (@preadditive_hom_zero C S B0 B2)))
  : τ (@= (Hom C A0 A2)
      (@comp_fapp0 C A0 A1 A2
        (@hom_postcomp_factor_arrow C A2 B2 A1 d2
          (@comp_fapp0 C A1 B1 B2 g d1) G)
        (@hom_postcomp_factor_arrow C A1 B1 A0 d1
          (@comp_fapp0 C A0 B0 B1 f d0) F))
      (@preadditive_hom_zero C S A0 A2))
≔ @monic_postcomposition_zero_to_zero_path C S A0 A2 B2
    d2 monic
    (@comp_fapp0 C A0 A1 A2
      (@hom_postcomp_factor_arrow C A2 B2 A1 d2
        (@comp_fapp0 C A1 B1 B2 g d1) G)
      (@hom_postcomp_factor_arrow C A1 B1 A0 d1
        (@comp_fapp0 C A0 B0 B1 f d0) F))
    (@eq_trans (Hom C A0 B2) _ _ _
      (@hom_postcomp_factor_path C A2 B2 A0 d2
        (@comp_fapp0 C A0 B0 B2 (@comp_fapp0 C B0 B1 B2 g f) d0)
        (@hom_postcomp_factor_paste C A0 B0 A1 B1 A2 B2
          d0 d1 d2 f g F G))
      (@preadditive_precompose_zero_path C S A0 B0 B2
        (@comp_fapp0 C B0 B1 B2 g f) d0 zero));

symbol epic_factor_postzero_path
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D X : τ (Obj C)]
  (e : τ (Hom C A B)) (u : τ (Hom C A D))
  (F : τ (@HomPrecompFactor C A B D e u))
  (epic : τ (@IsEpic C A B e))
  (h : τ (Hom C D X))
  (zero : τ (@= (Hom C A X) (@comp_fapp0 C A D X h u)
    (@preadditive_hom_zero C S A X)))
  : τ (@= (Hom C B X)
      (@comp_fapp0 C B D X h (@hom_precomp_factor_arrow C A B D e u F))
      (@preadditive_hom_zero C S B X))
≔ @epic_precomposition_zero_to_zero_path C S A B X e epic
    (@comp_fapp0 C B D X h (@hom_precomp_factor_arrow C A B D e u F))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _ (@comp_assoc C A B D X h
        (@hom_precomp_factor_arrow C A B D e u F) e))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C A D) (Hom C A X)
          (λ k : τ (Hom C A D), @comp_fapp0 C A D X h k) _ _
          (@hom_precomp_factor_path C A B D e u F))
        zero));
