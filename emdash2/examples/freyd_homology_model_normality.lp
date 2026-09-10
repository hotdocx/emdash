/* Supplied normality preserves the exact original choices and whole H. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_normality;

assert [R : τ CommRing] (M : τ (FreydHomologyModel R)) (N : τ (@FreydHomologyModelNormality R M)) ⊢
  (@freyd_homology_model_abelian R M N) : τ (@ComputationalAbelianCategory (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R));
assert [R : τ CommRing] (M : τ (FreydHomologyModel R)) (N : τ (@FreydHomologyModelNormality R M)) ⊢
  (@preabelian_kernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@computational_abelian_preabelian (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N))) ≡
  (@freyd_homology_model_kernels R M);
assert [R : τ CommRing] (M : τ (FreydHomologyModel R)) (N : τ (@FreydHomologyModelNormality R M)) ⊢
  (@preabelian_cokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@computational_abelian_preabelian (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N))) ≡
  (@freyd_homology_model_cokernels R M);
assert [R : τ CommRing] (M : τ (FreydHomologyModel R)) (N : τ (@FreydHomologyModelNormality R M)) ⊢
  (@zero_arrow_cone_homology_func (@CommRingFreydPresentation_cat R) (@computational_homology_preadditive
  (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R)
  (@computational_abelian_preabelian (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N))) (@comm_ring_freyd_cat_is_one_cat R)
  (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) (@freyd_homology_model_initial R M)
  (@preabelian_kernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@computational_abelian_preabelian (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N)))
  (@preabelian_cokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@computational_abelian_preabelian (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N)))
  (@freyd_homology_model_kernel_presentation R M) (@freyd_homology_model_cokernel_presentation R M)) ≡
  @freyd_homology_model_func R M;
assert [R : τ CommRing] (M : τ (FreydHomologyModel R)) (N : τ (@FreydHomologyModelNormality R M)) ⊢
  @computational_abelian_mono_lifts (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N) ≡ sigma_Fst N;
assert [R : τ CommRing] (M : τ (FreydHomologyModel R)) (N : τ (@FreydHomologyModelNormality R M)) ⊢
  @computational_abelian_epi_colifts (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N) ≡ sigma_Snd N;

// This constructor does not invent the missing normality algorithms.
assertnot [R : τ CommRing] (M : τ (FreydHomologyModel R)) ⊢
  @freyd_homology_model_abelian R M : τ (@ComputationalAbelianCategory (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R) (@comm_ring_zero_presentation R));
