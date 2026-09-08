/* Generic descent retains the original cokernel and its reconstruction. */
require open emdash.emdash3_2_cokernel_monic_factor_descent;

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A Q L R U Z : τ (Obj C))
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
  ⊢ (@cokernel_descend_monic_factor C S A Q L R U Z j delta v F monic b W s zero) : τ (@HomPrecompFactor C Z (@computational_cokernel_object C S U Z b W) A
    (@computational_cokernel_morphism C S U Z b W)
    (@comp_fapp0 C Z L A
      (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s));

assert
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A Q L R U Z : τ (Obj C))
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
  ⊢ @hom_precomp_factor_path C Z (@computational_cokernel_object C S U Z b W) A (@computational_cokernel_morphism C S U Z b W) (@comp_fapp0 C Z L A (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s) (@cokernel_descend_monic_factor C S A Q L R U Z j delta v F monic b W s zero)
    : τ (@= (Hom C Z A) (@comp_fapp0 C Z (@computational_cokernel_object C S U Z b W) A (@hom_precomp_factor_arrow C Z (@computational_cokernel_object C S U Z b W) A (@computational_cokernel_morphism C S U Z b W) (@comp_fapp0 C Z L A (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s) (@cokernel_descend_monic_factor C S A Q L R U Z j delta v F monic b W s zero)) (@computational_cokernel_morphism C S U Z b W)) (@comp_fapp0 C Z L A (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s));

assertnot
  (C : Cat) (S : τ (@PreadditiveCategory C))
  (A Q L R U Z : τ (Obj C))
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
  (other : τ (Hom C (@computational_cokernel_object C S U Z b W) A))
  ⊢ (@hom_precomp_factor_arrow C Z (@computational_cokernel_object C S U Z b W) A (@computational_cokernel_morphism C S U Z b W) (@comp_fapp0 C Z L A (@hom_postcomp_factor_arrow C A Q L j (@comp_fapp0 C L R Q v delta) F) s) (@cokernel_descend_monic_factor C S A Q L R U Z j delta v F monic b W s zero)) ≡ other;
