/*
  Abelian specialization: monic k induces a monic Coker(b) → Coker(k ∘ b).

  Existing selected pushout stability supplies the only monicity premise
  of the generic pushout-factor proof. No comparison property is postulated.
*/
require open emdash.emdash3_2_cokernel_composite_monic;
require open emdash.emdash3_2_abelian_fiber_pushout_stability;

// Keep the same literal preadditive presentation as the generic pushout proof.
// The shorter stability-preadditive alias exceeded the 90-second check bound.
symbol abelian_cokernel_composite_comparison_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A Z B : τ (Obj C)]
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C (@additive_preadditive C P t (@abelian_stability_additive C P t Ab)) A Z b))
  (Qf : τ (@ComputationalCokernel C (@additive_preadditive C P t (@abelian_stability_additive C P t Ab)) A B f))
  (monic : τ (@IsMonic C Z B k))
  : τ
    (@IsMonic C
      (@computational_cokernel_object C
        (@additive_preadditive C P t
          (@abelian_stability_additive C P t Ab)) A Z b Qb)
      (@computational_cokernel_object C
        (@additive_preadditive C P t
          (@abelian_stability_additive C P t Ab)) A B f Qf)
      (@cokernel_composite_comparison C
        (@additive_preadditive C P t
          (@abelian_stability_additive C P t Ab)) A Z B b k f factor Qb Qf))
≔ @cokernel_composite_comparison_monic_from_pushout
    C P t (@abelian_stability_additive C P t Ab) A Z B b k f factor Qb Qf
    (@abelian_selected_pushout C P t Ab Z B
        (@computational_cokernel_object C
          (@additive_preadditive C P t
            (@abelian_stability_additive C P t Ab)) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t
            (@abelian_stability_additive C P t Ab)) A Z b Qb))
    (@abelian_pushout_monic_injection C P t Ab Z B
        (@computational_cokernel_object C
          (@additive_preadditive C P t
            (@abelian_stability_additive C P t Ab)) A Z b Qb)
      k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t
            (@abelian_stability_additive C P t Ab)) A Z b Qb) monic);
