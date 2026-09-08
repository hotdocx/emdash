/* A chain law descends through an epic first component of two Hom factors. */
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol hom_precomp_factor_paste_zero_path
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A0 B0 A1 B1 A2 B2 : τ (Obj C)]
  (d0 : τ (Hom C A0 B0)) (d1 : τ (Hom C A1 B1))
  (d2 : τ (Hom C A2 B2))
  (f : τ (Hom C A0 A1)) (g : τ (Hom C A1 A2))
  (F : τ (@HomPrecompFactor C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f)))
  (G : τ (@HomPrecompFactor C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g)))
  (epic : τ (@IsEpic C A0 B0 d0))
  (zero : τ (@= (Hom C A0 A2) (@comp_fapp0 C A0 A1 A2 g f)
    (@preadditive_hom_zero C S A0 A2)))
  : τ (@= (Hom C B0 B2)
    (@comp_fapp0 C B0 B1 B2
      (@hom_precomp_factor_arrow C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g) G)
      (@hom_precomp_factor_arrow C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f) F))
    (@preadditive_hom_zero C S B0 B2))
≔ @epic_precomposition_zero_to_zero_path C S A0 B0 B2 d0 epic
    (@comp_fapp0 C B0 B1 B2
      (@hom_precomp_factor_arrow C A1 B1 B2 d1 (@comp_fapp0 C A1 A2 B2 d2 g) G)
      (@hom_precomp_factor_arrow C A0 B0 B1 d0 (@comp_fapp0 C A0 A1 B1 d1 f) F))
    (@eq_trans _ _ _ _
      (@hom_precomp_factor_path C A0 B0 B2 d0
        (@comp_fapp0 C A0 A2 B2 d2 (@comp_fapp0 C A0 A1 A2 g f))
        (@hom_precomp_factor_paste C A0 B0 A1 B1 A2 B2 d0 d1 d2 f g F G))
      (@preadditive_postcompose_zero_path C S A0 A2 B2
        d2 (@comp_fapp0 C A0 A1 A2 g f) zero));
