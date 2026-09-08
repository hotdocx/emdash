/* The actual row-snake lambda lift factors through the lower row source. */

require open emdash.emdash3_2_hom_factor_source_isos;
require open emdash.emdash3_2_chain_pair_map_snake;
require open emdash.emdash3_2_abelian_snake_normal_mono_foundation;
require open emdash.emdash3_2_short_exact_kernel_comparison;

// Abstract row data; every further comparison/factor below is constructed.
symbol C : Cat;
symbol P : τ (Functor (Product_cat C C) C);
symbol t : τ (Obj C);
symbol PA : τ (@PreAbelianCategory C P t);
symbol S : τ (@PreadditiveCategory C)
≔ @additive_preadditive C P t (@preabelian_additive C P t PA);
symbol M : τ (@HasLiftsAlongMonomorphisms C S (@preabelian_cokernels C P t PA));
symbol Epi : τ (@HasColiftsAlongEpimorphisms C S (@preabelian_kernels C P t PA));
symbol Ab : τ (@ComputationalAbelianCategory C P t)
≔ @computational_abelian_category_intro C P t PA M Epi;
symbol A0 : τ (Obj C);
symbol B0 : τ (Obj C);
symbol D0 : τ (Obj C);
symbol A1 : τ (Obj C);
symbol B1 : τ (Obj C);
symbol D1 : τ (Obj C);
symbol row0 : τ (@ComputationalChainPair C S A0 B0 D0);
symbol row1 : τ (@ComputationalChainPair C S A1 B1 D1);
symbol F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 row0 row1);
symbol short1 : τ (@ComputationalShortExactTriple C P t PA A1 B1 D1 row1);
symbol triple : τ (@AbelianSnakeTriple C S A0 B0 B1 D1)
≔ @chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 row0 row1 F;
symbol Krow : τ (Obj C)
≔ @abelian_snake_ker_lambda_object C P t Ab A0 B0 B1 D1 triple;
symbol Fiber : τ (Obj C)
≔ @abelian_snake_fiber_object C P t Ab A0 B0 B1 D1 triple;
symbol i : τ (Hom C A1 B1)
≔ @computational_chain_pair_dnext C S A1 B1 D1 row1;
symbol mu : τ (Hom C Krow B1)
≔ @abelian_snake_mu C P t Ab A0 B0 B1 D1 triple;
symbol L : τ (Hom C Fiber Krow)
≔ @abelian_snake_beta_p2_lambda_lift C P t Ab A0 B0 B1 D1 triple;
symbol beta_p2 : τ (Hom C Fiber B1)
≔ @abelian_snake_beta_p2 C P t Ab A0 B0 B1 D1 triple;
symbol a : τ (@IsoEvidence C A1 Krow)
≔ @short_exact_kernel_comparison_iso C P t Ab A1 B1 D1 row1 short1;
symbol comparison : τ (@= (Hom C A1 B1)
  (@comp_fapp0 C A1 Krow B1 mu (@iso_evidence_to C A1 Krow a)) i)
≔ @computational_homology_boundary_path C P t PA A1 B1 D1 row1
    (@computational_homology_at C P t PA A1 B1 D1 row1);
symbol original_factor : τ (@HomPostcompFactor C Krow B1 Fiber mu beta_p2)
≔ @hom_postcomp_factor_intro C Krow B1 Fiber mu beta_p2 L
    (@abelian_snake_beta_p2_lambda_lift_path C P t Ab A0 B0 B1 D1 triple);
symbol target_factor : τ (@HomPostcompFactor C A1 B1 Fiber i beta_p2)
≔ @hom_postcomp_factor_source_iso C A1 Krow B1 Fiber
    i mu a comparison beta_p2 original_factor;

// This is the factor needed by the neighboring-column cycle foundation.
assert ⊢ target_factor : τ (@HomPostcompFactor C A1 B1 Fiber i beta_p2);
assert ⊢ @hom_postcomp_factor_arrow C A1 B1 Fiber i beta_p2 target_factor
  ≡ @comp_fapp0 C Fiber Krow A1 (@iso_evidence_from C A1 Krow a) L;
assert ⊢ @hom_postcomp_factor_path C A1 B1 Fiber i beta_p2 target_factor
  : τ (@= (Hom C Fiber B1)
      (@comp_fapp0 C Fiber A1 B1 i
        (@comp_fapp0 C Fiber Krow A1 (@iso_evidence_from C A1 Krow a) L))
      beta_p2);
