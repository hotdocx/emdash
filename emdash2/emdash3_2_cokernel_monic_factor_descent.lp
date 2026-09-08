/* A monic lift inherits annihilation of the original arrow. */
require open emdash.emdash3_2_hom_factor_views;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

symbol monic_factor_prezero_path
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A Q L R T : τ (Obj C)]
  (j : τ (Hom C A Q)) (delta : τ (Hom C L R))
  (v : τ (Hom C R Q))
  (F : τ (@HomPostcompFactor C A Q L j (@comp_fapp0 C L R Q v delta)))
  (monic : τ (@IsMonic C A Q j))
  (b : τ (Hom C T L))
  (zero : τ (@= (Hom C T R) (@comp_fapp0 C T L R delta b)
    (@preadditive_hom_zero C S T R)))
  : τ (@= (Hom C T A)
    (@comp_fapp0 C T L A
      (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) b)
    (@preadditive_hom_zero C S T A))
≔ @monic_postcomposition_zero_to_zero_path C S T A Q j monic
    (@comp_fapp0 C T L A
      (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) b)
    (@eq_trans _ _ _ _
      (@comp_assoc C T L A Q j
        (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) b)
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C L Q) (Hom C T Q)
          (λ h : τ (Hom C L Q), @comp_fapp0 C T L Q h b) _ _
          (@hom_postcomp_factor_path C A Q L j (@comp_fapp0 C L R Q v delta) F))
        (@eq_trans _ _ _ _
          (@eq_sym _ _ _ (@comp_assoc C T L R Q v delta b))
          (@preadditive_postcompose_zero_path C S T R Q v
            (@comp_fapp0 C T L R delta b) zero))));

symbol cokernel_descend_monic_factor
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A Q L R U Z : τ (Obj C)]
  (j : τ (Hom C A Q)) (delta : τ (Hom C L R))
  (v : τ (Hom C R Q))
  (F : τ (@HomPostcompFactor C A Q L j (@comp_fapp0 C L R Q v delta)))
  (monic : τ (@IsMonic C A Q j))
  (b : τ (Hom C U Z))
  (W : τ (@ComputationalCokernel C S U Z b))
  (s : τ (Hom C Z L))
  (zero : τ (@= (Hom C U R)
    (@comp_fapp0 C U L R delta (@comp_fapp0 C U Z L s b))
    (@preadditive_hom_zero C S U R)))
  : τ (@HomPrecompFactor C Z (@computational_cokernel_object C S U Z b W) A
    (@computational_cokernel_morphism C S U Z b W)
    (@comp_fapp0 C Z L A
      (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s))
≔ is_contr_center (@computational_cokernel_factor_contr C S U Z b W A
    (@Struct_sigma (Hom C Z A)
      (λ h : τ (Hom C Z A), @= (Hom C U A)
        (@comp_fapp0 C U Z A h b) (@preadditive_hom_zero C S U A))
      (@comp_fapp0 C Z L A
        (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s)
      (@eq_trans _ _ _ _
        (@eq_sym _ _ _ (@comp_assoc C U Z L A
          (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s b))
        (@monic_factor_prezero_path C S A Q L R U j delta v F monic
          (@comp_fapp0 C U Z L s b) zero))));
