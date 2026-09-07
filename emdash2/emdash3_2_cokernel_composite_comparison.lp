/*
  The comparison Coker(b) → Coker(f) induced by f = k ∘ b.

  Both cokernels are existing whole universal constructions. The test and
  its zero proof are derived from the factorization and annihilation.
  Monicity is downstream; no rule, unifier, or comparison axiom is added.
*/

require open emdash.emdash3_2_kernels_cokernels;

// (pi_f ∘ k) ∘ b = pi_f ∘ f = 0.
symbol cokernel_composite_comparison_zero_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A Z B : τ (Obj C)]
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  : τ (@= (Hom C A (@computational_cokernel_object C S A B f Qf))
      (@comp_fapp0 C A Z (@computational_cokernel_object C S A B f Qf)
        (@comp_fapp0 C Z B
            (@computational_cokernel_object C S A B f Qf)
            (@computational_cokernel_morphism C S A B f Qf) k) b)
      (@preadditive_hom_zero C S A (@computational_cokernel_object C S A B f Qf)))
≔ (@eq_trans _ _ _ _
      (@eq_sym _ _ _
          (@comp_assoc C A Z B
            (@computational_cokernel_object C S A B f Qf)
            (@computational_cokernel_morphism C S A B f Qf) k b))
      (@eq_trans _ _ _ _
        (@eq_ap (Hom C A B) (Hom C A (@computational_cokernel_object C S A B f Qf))
          (λ h : τ (Hom C A B), @comp_fapp0 C A B
              (@computational_cokernel_object C S A B f Qf)
              (@computational_cokernel_morphism C S A B f Qf) h)
          _ _ factor)
        (@computational_cokernel_annihilation C S A B f Qf)));

// The induced coannihilator is computed, not supplied as a commuting square.
symbol cokernel_composite_comparison_cocone
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A Z B : τ (Obj C)]
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  : τ (@CokernelCoannihilator C S A Z b (@computational_cokernel_object C S A B f Qf))
≔ @Struct_sigma
    (Hom C Z (@computational_cokernel_object C S A B f Qf))
    (λ h : τ (Hom C Z (@computational_cokernel_object C S A B f Qf)),
      @= (Hom C A (@computational_cokernel_object C S A B f Qf))
        (@comp_fapp0 C A Z (@computational_cokernel_object C S A B f Qf) h b)
        (@preadditive_hom_zero C S A (@computational_cokernel_object C S A B f Qf)))
    (@comp_fapp0 C Z B
        (@computational_cokernel_object C S A B f Qf)
        (@computational_cokernel_morphism C S A B f Qf) k)
    (@cokernel_composite_comparison_zero_path C S A Z B b k f factor Qb Qf);

// Select the comparison from the original cokernel's contractible factor space.
symbol cokernel_composite_comparison
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A Z B : τ (Obj C)]
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  : τ (Hom C (@computational_cokernel_object C S A Z b Qb) (@computational_cokernel_object C S A B f Qf))
≔ @computational_cokernel_colift C S A Z b Qb (@computational_cokernel_object C S A B f Qf)
    (@cokernel_composite_comparison_cocone C S A Z B b k f factor Qb Qf);

// j ∘ q_b = pi_f ∘ k, at the literal selected colift.
symbol cokernel_composite_comparison_path
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A Z B : τ (Obj C)]
  (b : τ (Hom C A Z))
  (k : τ (Hom C Z B))
  (f : τ (Hom C A B))
  (factor : τ (@= (Hom C A B) (@comp_fapp0 C A Z B k b) f))
  (Qb : τ (@ComputationalCokernel C S A Z b))
  (Qf : τ (@ComputationalCokernel C S A B f))
  : τ (@= (Hom C Z (@computational_cokernel_object C S A B f Qf))
      (@comp_fapp0 C Z (@computational_cokernel_object C S A Z b Qb) (@computational_cokernel_object C S A B f Qf)
        (@cokernel_composite_comparison C S A Z B b k f factor Qb Qf)
          (@computational_cokernel_morphism C S A Z b Qb))
      (@comp_fapp0 C Z B
          (@computational_cokernel_object C S A B f Qf)
          (@computational_cokernel_morphism C S A B f Qf) k))
≔ @computational_cokernel_colift_path C S A Z b Qb (@computational_cokernel_object C S A B f Qf)
    (@cokernel_composite_comparison_cocone C S A Z B b k f factor Qb Qf);
