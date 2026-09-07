/*
  Monicity of the cokernel comparison from a monic pushout injection.

  Calculate after q_b, cancel its generic epicity, and apply the existing
  monic-factor lemma. The Abelian specialization supplies injection monicity
  from its already-proved pushout stability, not from a new axiom.
*/

require open emdash.emdash3_2_cokernel_composite_pushout;

// (s ∘ j) ∘ q_b = inj2 ∘ q_b.
symbol cokernel_composite_pushout_comparison_after_q_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Sa : τ (@AdditiveCategory C P t))
  [A Z B : τ (Obj C)]
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
  : τ
    (@= (Hom C Z
        (@computational_pushout_object C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO))
      (@comp_fapp0 C Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb)
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO)
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
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb))
      (@comp_fapp0 C Z
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
              (@additive_preadditive C P t Sa) A Z b Qb) PO)
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb)))
≔ (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C Z
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
              (@additive_preadditive C P t Sa) A Z B b k f factor Qb Qf)
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb)))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A B f Qf)) (Hom C Z
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO))
        (λ h : τ (Hom C Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A B f Qf)), @comp_fapp0 C Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A B f Qf)
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO)
            (@cokernel_composite_pushout_factor C P t Sa A Z B b k f factor Qb Qf PO) h)
        _ _ (@cokernel_composite_comparison_path C (@additive_preadditive C P t Sa) A Z B b k f factor Qb Qf))
      (@eq_trans _ _ _ _
      (@comp_assoc C Z B
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A B f Qf)
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO)
          (@cokernel_composite_pushout_factor C P t Sa A Z B b k f factor Qb Qf PO)
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A B f Qf) k)
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C B
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO)) (Hom C Z
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO))
        (λ h : τ (Hom C B
              (@computational_pushout_object C P t Sa B Z
                (@computational_cokernel_object C
                  (@additive_preadditive C P t Sa) A Z b Qb) k
                (@computational_cokernel_morphism C
                  (@additive_preadditive C P t Sa) A Z b Qb) PO)), @comp_fapp0 C Z B
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO) h k)
        _ _ (@cokernel_composite_pushout_factor_path C P t Sa A Z B b k f factor Qb Qf PO))
      (@computational_pushout_compatibility_path C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO)))));

// Cancel the original cokernel projection: s ∘ j = inj2.
symbol cokernel_composite_pushout_comparison_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Sa : τ (@AdditiveCategory C P t))
  [A Z B : τ (Obj C)]
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
          (@additive_preadditive C P t Sa) A Z b Qb) PO))
≔ (@computational_cokernel_morphism_is_epic C (@additive_preadditive C P t Sa) A Z b Qb)
    (@computational_pushout_object C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb) PO)
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
          (@additive_preadditive C P t Sa) A Z b Qb) PO)
    (@cokernel_composite_pushout_comparison_after_q_path C P t Sa A Z B b k f factor Qb Qf PO);

// A factor of a monic injection is monic.
symbol cokernel_composite_comparison_monic_from_pushout
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Sa : τ (@AdditiveCategory C P t))
  [A Z B : τ (Obj C)]
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
  (injection_monic : τ
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
  : τ
    (@IsMonic C
      (@computational_cokernel_object C
        (@additive_preadditive C P t Sa) A Z b Qb)
      (@computational_cokernel_object C
        (@additive_preadditive C P t Sa) A B f Qf)
      (@cokernel_composite_comparison C
        (@additive_preadditive C P t Sa) A Z B b k f factor Qb Qf))
≔ @is_monic_of_monic_factor C
  (@computational_cokernel_object C
    (@additive_preadditive C P t Sa) A Z b Qb)
  (@computational_cokernel_object C
    (@additive_preadditive C P t Sa) A B f Qf)
  (@computational_pushout_object C P t Sa B Z
    (@computational_cokernel_object C
      (@additive_preadditive C P t Sa) A Z b Qb) k
    (@computational_cokernel_morphism C
      (@additive_preadditive C P t Sa) A Z b Qb) PO)
    (@cokernel_composite_comparison C
        (@additive_preadditive C P t Sa) A Z B b k f factor Qb Qf)
      (@cokernel_composite_pushout_factor C P t Sa A Z B b k f factor Qb Qf PO)
      (@computational_pushout_inj2 C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb) PO)
    (@cokernel_composite_pushout_comparison_path C P t Sa A Z B b k f factor Qb Qf PO)
    injection_monic;
