/* Exactness supplies the normal-epi test for the inverse comparison. */

require open emdash.emdash3_2_short_exact_cokernel_foundation;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// The selected cokernel kills the cycle embedding after the epic boundary.
symbol short_exact_cokernel_cycle_after_boundary_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  : τ (@= (Hom C A (@short_exact_cokernel_object C P t Ab A B D pair)) (@comp_fapp0 C _ _ _
    (@comp_fapp0 C _ _ _ (@short_exact_cokernel_projection C P t Ab A B D pair)
    (@computational_homology_cycle_embedding C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair)))
    (@short_exact_kernel_comparison C P t Ab A B D pair))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A
        (@short_exact_cokernel_object C P t Ab A B D pair)))
≔ @eq_trans _ _ _ _
    (@eq_sym _ _ _ (@comp_assoc C _ _ _ _ (@short_exact_cokernel_projection C P t Ab A B D pair)
      (@computational_homology_cycle_embedding C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair))
      (@short_exact_kernel_comparison C P t Ab A B D pair)))
    (@eq_trans _ _ _ _
      (@eq_ap (Hom C A B) (Hom C A (@short_exact_cokernel_object C P t Ab A B D pair))
        (λ h : τ (Hom C A B), (@comp_fapp0 C _ _ _
          (@short_exact_cokernel_projection C P t Ab A B D pair) h))
        _ _ (@computational_homology_boundary_path C P t
          (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
          (@computational_abelian_preabelian C P t Ab) A B D pair)))
      (@computational_cokernel_annihilation C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B (@computational_chain_pair_dnext C
        (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair)
        (@short_exact_incoming_cokernel C P t Ab A B D pair)));

symbol short_exact_cokernel_cycle_zero_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@= (Hom C (@computational_homology_cycle_object C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
    (@short_exact_cokernel_object C P t Ab A B D pair)) (@comp_fapp0 C _ _ _
    (@short_exact_cokernel_projection C P t Ab A B D pair)
    (@computational_homology_cycle_embedding C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair)))
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) (@computational_homology_cycle_object C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair))
        (@short_exact_cokernel_object C P t Ab A B D pair)))
≔ @epic_precomposition_zero_to_zero_path C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A (@computational_homology_cycle_object C P t
  (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
  (@computational_abelian_preabelian C P t Ab) A B D pair))
  (@short_exact_cokernel_object C P t Ab A B D pair)
    (@short_exact_kernel_comparison C P t Ab A B D pair)
    (@computational_short_exact_boundary_epic C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair short)
    (@comp_fapp0 C _ _ _ (@short_exact_cokernel_projection C P t Ab A B D pair)
      (@computational_homology_cycle_embedding C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair)))
    (@short_exact_cokernel_cycle_after_boundary_zero_path C P t Ab A B D pair);

symbol short_exact_cokernel_inverse_test
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D))
  (short : τ (@ComputationalShortExactTriple C P t
    (@computational_abelian_preabelian C P t Ab) A B D pair))
  : τ (@NormalEpiTest C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) B D (@computational_chain_pair_d C
    (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B D pair)
      (@preabelian_kernel C P t (@computational_abelian_preabelian C P t Ab) B D
        (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A B D pair))
        (@short_exact_cokernel_object C P t Ab A B D pair))
≔ @Struct_sigma (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair))
    (λ h : τ (Hom C B (@short_exact_cokernel_object C P t Ab A B D pair)), @= (Hom C
      (@computational_homology_cycle_object C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
      (@computational_abelian_preabelian C P t Ab) A B D pair))
      (@short_exact_cokernel_object C P t Ab A B D pair))
      (@comp_fapp0 C _ _ _ h (@computational_homology_cycle_embedding C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair))) (@preadditive_hom_zero C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@computational_homology_cycle_object C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair (@computational_homology_at C P t
        (@computational_abelian_preabelian C P t Ab) A B D pair))
        (@short_exact_cokernel_object C P t Ab A B D pair)))
    (@short_exact_cokernel_projection C P t Ab A B D pair)
    (@short_exact_cokernel_cycle_zero_path C P t Ab A B D pair short);
