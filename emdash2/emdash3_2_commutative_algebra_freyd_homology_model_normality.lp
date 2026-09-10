/*
  Add supplied normality to the original coherent homology model.
  The original W/V and their presentations are retained definitionally.
  This is not synthesis of a closed Freyd provider from raw agreements.
*/
require open emdash.emdash3_2_commutative_algebra_freyd_homology_models;
require open emdash.emdash3_2_commutative_algebra_freyd_additive;
require open emdash.emdash3_2_abelian_categories;

symbol freyd_homology_model_preabelian [R : τ CommRing]
  (M : τ (FreydHomologyModel R))
  : τ (@PreAbelianCategory (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R))
≔ @preabelian_category_intro (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_additive R) (@freyd_homology_model_kernels R M) (@freyd_homology_model_cokernels R M);

symbol FreydHomologyModelNormality [R : τ CommRing]
  (M : τ (FreydHomologyModel R)) : Grpd
≔ @Product_grpd (@HasLiftsAlongMonomorphisms (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@freyd_homology_model_cokernels R M)) (@HasColiftsAlongEpimorphisms (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@freyd_homology_model_kernels R M));

symbol freyd_homology_model_normality_intro [R : τ CommRing]
  (M : τ (FreydHomologyModel R))
  (mono : τ (@HasLiftsAlongMonomorphisms (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    (@freyd_homology_model_cokernels R M))) (epi : τ (@HasColiftsAlongEpimorphisms (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@freyd_homology_model_kernels R M)))
  : τ (@FreydHomologyModelNormality R M)
≔ @Product_pair_grpd (@HasLiftsAlongMonomorphisms (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
  (@freyd_homology_model_cokernels R M)) (@HasColiftsAlongEpimorphisms (@CommRingFreydPresentation_cat R)
  (@comm_ring_freyd_preadditive R) (@freyd_homology_model_kernels R M)) mono epi;

symbol freyd_homology_model_abelian [R : τ CommRing]
  (M : τ (FreydHomologyModel R))
  (N : τ (@FreydHomologyModelNormality R M))
  : τ (@ComputationalAbelianCategory (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R))
≔ @computational_abelian_category_intro (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R)
    (@freyd_homology_model_preabelian R M) (sigma_Fst N) (sigma_Snd N);
