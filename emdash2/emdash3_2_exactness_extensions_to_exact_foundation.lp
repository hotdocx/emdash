/* Boundary cokernel and pushout used by the extension-to-exactness theorem. */

require open emdash.emdash3_2_exactness_extensions_foundation;
require open emdash.emdash3_2_abelian_fiber_pushout_stability;

symbol computational_exact_boundary_cokernel
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@ComputationalCokernel C
      (@abelian_stability_preadditive C P t Ab)
      A
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_homology_boundary C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H))
≔ (@abelian_stability_cokernels C P t Ab)
    A
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H);

symbol computational_exact_boundary_cokernel_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@abelian_stability_preadditive C P t Ab)
    A
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel C P t Ab A B D pair H);

symbol computational_exact_boundary_cokernel_projection
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (Hom C
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_exact_boundary_cokernel_object C P t
        Ab A B D pair H))
≔ @computational_cokernel_morphism C
    (@abelian_stability_preadditive C P t Ab)
    A
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_homology_boundary C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel C P t Ab A B D pair H);

symbol computational_exact_boundary_pushout
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@ComputationalPushout C P t
      (@abelian_stability_additive C P t Ab)
      B
      (@computational_homology_cycle_object C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_exact_boundary_cokernel_object C P t
        Ab A B D pair H)
      (@computational_homology_cycle_embedding C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H)
      (@computational_exact_boundary_cokernel_projection C P t
        Ab A B D pair H))
≔ @abelian_selected_pushout C P t Ab
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    B
    (@computational_exact_boundary_cokernel_object C P t
      Ab A B D pair H)
    (@computational_homology_cycle_embedding C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_projection C P t
      Ab A B D pair H);

symbol computational_exact_boundary_pushout_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (Obj C)
≔ @computational_pushout_object C P t
    (@abelian_stability_additive C P t Ab)
    B
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_object C P t
      Ab A B D pair H)
    (@computational_homology_cycle_embedding C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_projection C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout C P t Ab A B D pair H);

symbol computational_exact_boundary_pushout_inj1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (Hom C B
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H))
≔ @computational_pushout_inj1 C P t
    (@abelian_stability_additive C P t Ab)
    B
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_object C P t
      Ab A B D pair H)
    (@computational_homology_cycle_embedding C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_projection C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout C P t Ab A B D pair H);

symbol computational_exact_boundary_pushout_inj2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [Ab : τ (@ComputationalAbelianCategory C P t)]
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (Hom C
      (@computational_exact_boundary_cokernel_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H))
≔ @computational_pushout_inj2 C P t
    (@abelian_stability_additive C P t Ab)
    B
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_object C P t
      Ab A B D pair H)
    (@computational_homology_cycle_embedding C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_projection C P t
      Ab A B D pair H)
    (@computational_exact_boundary_pushout C P t Ab A B D pair H);

symbol computational_exact_boundary_pushout_inj2_monic
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B D : τ (Obj C)]
  [pair : τ (@ComputationalChainPair C
    (@abelian_stability_preadditive C P t Ab) A B D)]
  (H : τ (@ComputationalHomologyAt C P t
    (@abelian_stability_preabelian C P t Ab) A B D pair))
  : τ (@IsMonic C
      (@computational_exact_boundary_cokernel_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_object C P t
        Ab A B D pair H)
      (@computational_exact_boundary_pushout_inj2 C P t
        Ab A B D pair H))
≔ @abelian_pushout_monic_injection C P t Ab
    (@computational_homology_cycle_object C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    B
    (@computational_exact_boundary_cokernel_object C P t
      Ab A B D pair H)
    (@computational_homology_cycle_embedding C P t
      (@abelian_stability_preabelian C P t Ab) A B D pair H)
    (@computational_exact_boundary_cokernel_projection C P t
      Ab A B D pair H)
    (@computational_kernel_morphism_is_monic C
      (@abelian_stability_preadditive C P t Ab)
      B D
      (@computational_chain_pair_d C
        (@abelian_stability_preadditive C P t Ab) A B D pair)
      (@computational_homology_cycles C P t
        (@abelian_stability_preabelian C P t Ab) A B D pair H));
