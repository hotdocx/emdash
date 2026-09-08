/* Parametric three-row API retains supplied homology cycles and reconstruction. */
require open emdash.emdash3_2_snake_row_target_cycles;

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
symbol A2 : τ (Obj C);
symbol B2 : τ (Obj C);
symbol D2 : τ (Obj C);
symbol whole0 : τ (@ComputationalShortExactRow C P t PA A0 B0 D0);
symbol row0 : τ (@ComputationalChainPair C S A0 B0 D0)
≔ @computational_short_exact_row_pair C P t PA A0 B0 D0 whole0;
symbol i0 : τ (Hom C A0 B0)
≔ @computational_chain_pair_dnext C S A0 B0 D0 row0;
symbol whole1 : τ (@ComputationalShortExactRow C P t PA A1 B1 D1);
symbol row1 : τ (@ComputationalChainPair C S A1 B1 D1)
≔ @computational_short_exact_row_pair C P t PA A1 B1 D1 whole1;
symbol i1 : τ (Hom C A1 B1)
≔ @computational_chain_pair_dnext C S A1 B1 D1 row1;
symbol whole2 : τ (@ComputationalShortExactRow C P t PA A2 B2 D2);
symbol row2 : τ (@ComputationalChainPair C S A2 B2 D2)
≔ @computational_short_exact_row_pair C P t PA A2 B2 D2 whole2;
symbol i2 : τ (Hom C A2 B2)
≔ @computational_chain_pair_dnext C S A2 B2 D2 row2;
symbol F : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 row0 row1);
symbol G : τ (@ComputationalChainPairMap C S A1 B1 D1 A2 B2 D2 row1 row2);
symbol a01 : τ (Hom C A0 A1)
≔ @computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 row0 row1 F;
symbol a12 : τ (Hom C A1 A2)
≔ @computational_chain_pair_map_next C S A1 B1 D1 A2 B2 D2 row1 row2 G;
symbol b01 : τ (Hom C B0 B1)
≔ @computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 row0 row1 F;
symbol b12 : τ (Hom C B1 B2)
≔ @computational_chain_pair_map_middle C S A1 B1 D1 A2 B2 D2 row1 row2 G;

// Required middle-column chain law; no row comparison equation is assumed.
symbol middle_zero : τ (@= (Hom C B0 B2)
  (@comp_fapp0 C B0 B1 B2 b12 b01) (@preadditive_hom_zero C S B0 B2));
symbol i2_monic : τ (@IsMonic C A2 B2 i2)
≔ @computational_short_exact_monic C P t PA A2 B2 D2 row2
    (@computational_short_exact_row_evidence C P t PA A2 B2 D2 whole2);

// i2 a12 a01 = b12 i1 a01 = b12 b01 i0 = 0, then cancel i2.
symbol source_zero : τ (@= (Hom C A0 A2)
  (@comp_fapp0 C A0 A1 A2 a12 a01) (@preadditive_hom_zero C S A0 A2))
≔ @short_exact_row_chain_source_zero_path C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 whole0 whole1 whole2 F G middle_zero;

// Construct the two column views from the original row-map components.
symbol columnA : τ (@ComputationalChainPair C S A0 A1 A2)
≔ @short_exact_row_chain_source_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 whole0 whole1 whole2 F G middle_zero;
symbol columnB : τ (@ComputationalChainPair C S B0 B1 B2)
≔ @short_exact_row_chain_middle_pair C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 whole0 whole1 whole2 F G middle_zero;
symbol inclusion : τ (@ComputationalChainPairMap C S A0 A1 A2 B0 B1 B2 columnA columnB)
≔ @short_exact_row_chain_inclusion C P t PA A0 B0 D0 A1 B1 D1 A2 B2 D2 whole0 whole1 whole2 F G middle_zero;

// This whole homology is supplied, not recomputed at a new kernel choice.
symbol H_A : τ (@ComputationalHomologyAt C P t PA A0 A1 A2 columnA);
symbol actual_cycles : τ (@ComputationalKernel C S A1 A2 a12)
≔ @computational_homology_cycles C P t PA A0 A1 A2 columnA H_A;
symbol actual_cycle_object : τ (Obj C)
≔ @computational_homology_cycle_object C P t PA A0 A1 A2 columnA H_A;
symbol actual_cycle_embedding : τ (Hom C actual_cycle_object A1)
≔ @computational_homology_cycle_embedding C P t PA A0 A1 A2 columnA H_A;

// The snake uses precisely the first two original rows and their original F.
symbol triple : τ (@AbelianSnakeTriple C S A0 B0 B1 D1)
≔ @chain_pair_map_snake_triple C S A0 B0 D0 A1 B1 D1 row0 row1 F;
symbol Krow : τ (Obj C)
≔ @abelian_snake_ker_lambda_object C P t Ab A0 B0 B1 D1 triple;
symbol Fiber : τ (Obj C)
≔ @abelian_snake_fiber_object C P t Ab A0 B0 B1 D1 triple;
symbol mu : τ (Hom C Krow B1)
≔ @abelian_snake_mu C P t Ab A0 B0 B1 D1 triple;
symbol L : τ (Hom C Fiber Krow)
≔ @abelian_snake_beta_p2_lambda_lift C P t Ab A0 B0 B1 D1 triple;
symbol p2 : τ (Hom C Fiber B0)
≔ @abelian_snake_p2 C P t Ab A0 B0 B1 D1 triple;
symbol beta_p2 : τ (Hom C Fiber B1)
≔ @abelian_snake_beta_p2 C P t Ab A0 B0 B1 D1 triple;
symbol a : τ (@IsoEvidence C A1 Krow)
≔ @short_exact_kernel_comparison_iso C P t Ab A1 B1 D1 row1
    (@computational_short_exact_row_evidence C P t PA A1 B1 D1 whole1);
symbol target_factor : τ (@HomPostcompFactor C A1 B1 Fiber i1 beta_p2)
≔ @snake_row_target_factor C P t PA M Epi A0 B0 D0 A1 B1 D1 whole0 whole1 F;

// Actually apply the generic lift to this snake factor and H_A's own cycles.
symbol actual_cycle_lift : τ (Hom C Fiber actual_cycle_object)
≔ @hom_postcomp_factor_arrow C actual_cycle_object A1 Fiber actual_cycle_embedding
    (@hom_postcomp_factor_arrow C A1 B1 Fiber i1 beta_p2 target_factor) (@snake_row_target_cycle_factor C P t PA M Epi A0 B0 D0 A1 B1 D1 A2 B2 D2 whole0 whole1 whole2 F G middle_zero H_A);
symbol actual_cycle_path : τ (@= (Hom C Fiber A1)
  (@comp_fapp0 C Fiber actual_cycle_object A1 actual_cycle_embedding actual_cycle_lift)
  (@comp_fapp0 C Fiber Krow A1 (@iso_evidence_from C A1 Krow a) L))
≔ @hom_postcomp_factor_path C actual_cycle_object A1 Fiber actual_cycle_embedding
    (@hom_postcomp_factor_arrow C A1 B1 Fiber i1 beta_p2 target_factor) (@snake_row_target_cycle_factor C P t PA M Epi A0 B0 D0 A1 B1 D1 A2 B2 D2 whole0 whole1 whole2 F G middle_zero H_A);

assert ⊢ @computational_chain_pair_map_middle C S A0 A1 A2 B0 B1 B2 columnA columnB inclusion ≡ i1;
assert ⊢ @computational_chain_pair_map_prev C S A0 A1 A2 B0 B1 B2 columnA columnB inclusion ≡ i2;
assert ⊢ @computational_chain_pair_dnext C S B0 B1 B2 columnB ≡ b01;
assert ⊢ actual_cycle_lift : τ (Hom C Fiber actual_cycle_object);
assert ⊢ actual_cycle_path : τ (@= (Hom C Fiber A1)
  (@comp_fapp0 C Fiber actual_cycle_object A1 actual_cycle_embedding actual_cycle_lift)
  (@comp_fapp0 C Fiber Krow A1 (@iso_evidence_from C A1 Krow a) L));
assertnot ⊢ actual_cycle_lift : τ (Hom C Fiber Krow);
