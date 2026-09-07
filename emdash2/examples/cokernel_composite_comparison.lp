/* Generic comparison, reconstruction, and wrong-cokernel consumers. */
require open emdash.emdash3_2_abelian_cokernel_composite_monic;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  ⊢
    (@cokernel_composite_comparison C S A Z B b k f factor Qb Qf) : τ (Hom C
      (@computational_cokernel_object C S A Z b Qb)
      (@computational_cokernel_object C S A B f Qf));

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  ⊢ @cokernel_coannihilator_arrow C S A Z b (@computational_cokernel_object C S A B f Qf)
      (@cokernel_composite_comparison_cocone C S A Z B b k f factor Qb Qf)
  ≡ @comp_fapp0 C Z B
    (@computational_cokernel_object C S A B f Qf)
    (@computational_cokernel_morphism C S A B f Qf) k;

assert
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  ⊢ @cokernel_composite_comparison_path C S A Z B b k f factor Qb Qf
  : τ (@= (Hom C Z (@computational_cokernel_object C S A B f Qf))
      (@comp_fapp0 C Z
          (@computational_cokernel_object C S A Z b Qb)
          (@computational_cokernel_object C S A B f Qf)
          (@cokernel_composite_comparison C S A Z B b k f factor Qb Qf)
          (@computational_cokernel_morphism C S A Z b Qb))
      (@comp_fapp0 C Z B
          (@computational_cokernel_object C S A B f Qf)
          (@computational_cokernel_morphism C S A B f Qf) k));

assertnot
  (C : Cat)
  (S : τ (@PreadditiveCategory C))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  (Qother : τ (@ComputationalCokernel C S A Z b))
  ⊢
    (@cokernel_composite_comparison C S A Z B b k f factor Qb Qf) : τ (Hom C
      (@computational_cokernel_object C S A Z b Qother)
      (@computational_cokernel_object C S A B f Qf));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Sa : τ (@AdditiveCategory C P t))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C (@additive_preadditive C P t Sa) A Z b))
  (Qf : τ (@ComputationalCokernel C (@additive_preadditive C P t Sa) A B f))
  (PO : τ
      (@ComputationalPushout C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb)))
  ⊢ @cokernel_composite_pushout_comparison_path C P t Sa A Z B b k f factor Qb Qf PO
  : τ
    (@= (Hom C
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb)
        (@computational_pushout_object C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO))
      (@comp_fapp0 C
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb)
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A B f Qf)
        (@computational_pushout_object C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO)
        (@cokernel_composite_pushout_factor C P t Sa A Z B b k f factor Qb Qf PO)
        (@cokernel_composite_comparison C
          (@additive_preadditive C P t Sa) A Z B b k f factor Qb Qf))
      (@computational_pushout_inj2 C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb) PO));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Sa : τ (@AdditiveCategory C P t))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C (@additive_preadditive C P t Sa) A Z b))
  (Qf : τ (@ComputationalCokernel C (@additive_preadditive C P t Sa) A B f))
  (PO : τ
      (@ComputationalPushout C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb)))
  (monic : τ
      (@IsMonic C
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb)
        (@computational_pushout_object C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO)
        (@computational_pushout_inj2 C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO)))
  ⊢ @cokernel_composite_comparison_monic_from_pushout C P t Sa A Z B b k f factor Qb Qf PO monic
  : τ
    (@IsMonic C
      (@computational_cokernel_object C
        (@additive_preadditive C P t Sa) A Z b Qb)
      (@computational_cokernel_object C
        (@additive_preadditive C P t Sa) A B f Qf)
      (@cokernel_composite_comparison C
        (@additive_preadditive C P t Sa) A Z B b k f factor Qb Qf));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (Ab : τ (@ComputationalAbelianCategory C P t))
  (A Z B : τ (Obj C))
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C (@additive_preadditive C P t (@abelian_stability_additive C P t Ab)) A Z b))
  (Qf : τ (@ComputationalCokernel C (@additive_preadditive C P t (@abelian_stability_additive C P t Ab)) A B f))
  (monic : τ (@IsMonic C Z B k))
  ⊢ @abelian_cokernel_composite_comparison_monic C P t Ab A Z B b k f factor Qb Qf monic
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
          (@abelian_stability_additive C P t Ab)) A Z B b k f factor Qb Qf));
