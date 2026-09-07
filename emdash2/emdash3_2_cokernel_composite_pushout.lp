/*
  Pushout factor of the cokernel-composite comparison.

  For f = k ∘ b, an actual pushout of k and q_b supplies a map from Coker(f).
  The reconstruction gives s ∘ j = inj2 after cancelling the epic q_b.
  Monicity of that injection therefore implies monicity of j.
*/

require open emdash.emdash3_2_cokernel_composite_comparison;
require open emdash.emdash3_2_computational_pushouts;
require open emdash.emdash3_2_mono_epi_comparisons;

// inj1 ∘ f = inj2 ∘ q_b ∘ b = 0.
symbol cokernel_composite_pushout_zero_path
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
    (@= (Hom C A
        (@computational_pushout_object C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO))
      (@comp_fapp0 C A B
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO)
          (@computational_pushout_inj1 C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO) f)
      (@preadditive_hom_zero C
          (@additive_preadditive C P t Sa) A
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO)))
≔ (@eq_trans _ _ _ _
      (@eq_ap (Hom C A B) (Hom C A
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO))
        (λ h : τ (Hom C A B), @comp_fapp0 C A B
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO)
            (@computational_pushout_inj1 C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO) h)
        _ _ (@eq_sym _ _ _ factor))
      (@eq_trans _ _ _ _
      (@comp_assoc C A Z B
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO)
          (@computational_pushout_inj1 C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO) k b)
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C Z
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO)) (Hom C A
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO))
        (λ h : τ (Hom C Z
              (@computational_pushout_object C P t Sa B Z
                (@computational_cokernel_object C
                  (@additive_preadditive C P t Sa) A Z b Qb) k
                (@computational_cokernel_morphism C
                  (@additive_preadditive C P t Sa) A Z b Qb) PO)), @comp_fapp0 C A Z
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO) h b)
        _ _
          (@computational_pushout_compatibility_path C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO))
      (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C A Z
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
              (@additive_preadditive C P t Sa) A Z b Qb) b))
      (@eq_trans _ _ _ _
      (@eq_ap (Hom C A
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb)) (Hom C A
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO))
        (λ h : τ (Hom C A
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb)), @comp_fapp0 C A
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
                (@additive_preadditive C P t Sa) A Z b Qb) PO) h)
        _ _ (@computational_cokernel_annihilation C (@additive_preadditive C P t Sa) A Z b Qb))
      (@preadditive_comp_zero_right_path C
          (@additive_preadditive C P t Sa) A
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
              (@additive_preadditive C P t Sa) A Z b Qb) PO)))))));

// The pushout injection determines a derived cokernel test.
symbol cokernel_composite_pushout_cocone
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
    (@CokernelCoannihilator C
      (@additive_preadditive C P t Sa) A B f
      (@computational_pushout_object C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb) PO))
≔ @Struct_sigma (Hom C B
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
              (@additive_preadditive C P t Sa) A Z b Qb) PO)),
      @= (Hom C A
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO))
        (@comp_fapp0 C A B
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO) h f)
        (@preadditive_hom_zero C
            (@additive_preadditive C P t Sa) A
            (@computational_pushout_object C P t Sa B Z
              (@computational_cokernel_object C
                (@additive_preadditive C P t Sa) A Z b Qb) k
              (@computational_cokernel_morphism C
                (@additive_preadditive C P t Sa) A Z b Qb) PO)))
    (@computational_pushout_inj1 C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb) PO)
    (@cokernel_composite_pushout_zero_path C P t Sa A Z B b k f factor Qb Qf PO);

// s : Coker(f) → PO selected from its original contractible factor space.
symbol cokernel_composite_pushout_factor
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
  : τ (Hom C
      (@computational_cokernel_object C
        (@additive_preadditive C P t Sa) A B f Qf)
      (@computational_pushout_object C P t Sa B Z
        (@computational_cokernel_object C
          (@additive_preadditive C P t Sa) A Z b Qb) k
        (@computational_cokernel_morphism C
          (@additive_preadditive C P t Sa) A Z b Qb) PO))
≔ @computational_cokernel_colift C
  (@additive_preadditive C P t Sa) A B f Qf
  (@computational_pushout_object C P t Sa B Z
    (@computational_cokernel_object C
      (@additive_preadditive C P t Sa) A Z b Qb) k
    (@computational_cokernel_morphism C
      (@additive_preadditive C P t Sa) A Z b Qb) PO)
    (@cokernel_composite_pushout_cocone C P t Sa A Z B b k f factor Qb Qf PO);

// s ∘ pi_f = inj1.
symbol cokernel_composite_pushout_factor_path
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
    (@= (Hom C B
        (@computational_pushout_object C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO))
      (@comp_fapp0 C B
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A B f Qf)
          (@computational_pushout_object C P t Sa B Z
            (@computational_cokernel_object C
              (@additive_preadditive C P t Sa) A Z b Qb) k
            (@computational_cokernel_morphism C
              (@additive_preadditive C P t Sa) A Z b Qb) PO)
        (@cokernel_composite_pushout_factor C P t Sa A Z B b k f factor Qb Qf PO)
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A B f Qf))
      (@computational_pushout_inj1 C P t Sa B Z
          (@computational_cokernel_object C
            (@additive_preadditive C P t Sa) A Z b Qb) k
          (@computational_cokernel_morphism C
            (@additive_preadditive C P t Sa) A Z b Qb) PO))
≔ @computational_cokernel_colift_path C
  (@additive_preadditive C P t Sa) A B f Qf
  (@computational_pushout_object C P t Sa B Z
    (@computational_cokernel_object C
      (@additive_preadditive C P t Sa) A Z b Qb) k
    (@computational_cokernel_morphism C
      (@additive_preadditive C P t Sa) A Z b Qb) PO)
    (@cokernel_composite_pushout_cocone C P t Sa A Z B b k f factor Qb Qf PO);
