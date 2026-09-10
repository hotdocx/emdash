/* Direct connecting computation in one supplied coherent Freyd model.
   The original raw maps/agreements and H selections are retained. Model
   normality and model-side short-exact witnesses are explicit inputs;
   no closed quotient effectiveness is inferred from finite raw data. */
/* The generic model-side short-exact predicate is explicit. It is not
   inferred from the older witness-enriched raw Freyd row package. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_normality;
require open emdash.emdash3_2_short_exact_rows;

symbol FreydHomologyModelShortExact [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d)) : Grpd
≔ @ComputationalShortExactTriple (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@freyd_homology_model_preabelian R M) A B D (@freyd_raw_chain_pair_generic R A B D e d
  chain);

symbol freyd_homology_model_short_exact_row [R : τ CommRing] (M : τ (FreydHomologyModel R))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  (exact : τ (@FreydHomologyModelShortExact R M A B D e d chain))
  : τ (@ComputationalShortExactRow (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R) (@freyd_homology_model_preabelian R M) A B D)
≔ @computational_short_exact_row_intro (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@freyd_homology_model_preabelian R M) A B D
    (@freyd_raw_chain_pair_generic R A B D e d chain) exact;

/* Direct model connecting component, retaining BOTH original H points.
   Normality and model-side row evidence remain supplied explicitly. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_records;
require open emdash.emdash3_2_homology_record_connecting;

symbol freyd_homology_model_connecting [R : τ CommRing]
  (M : τ (FreydHomologyModel R))
  (N : τ (@FreydHomologyModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydHomologyModelShortExact R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydHomologyModelShortExact R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydHomologyModelShortExact R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydHomologyModelShortExact R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
  (source_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0))
  (target_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
  : τ (@CommRingFreydHomSet R (@freyd_homology_model_object R M Dm D0 D1 dm d0 source_chain) (@freyd_homology_model_object R
    M A0 A1 A2 a0 a1 target_chain))
≔ @homology_record_connecting (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_direct_sum_func R)
  (@comm_ring_zero_presentation R) (@freyd_homology_model_abelian R M N) Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2
  (@freyd_homology_model_short_exact_row R M Am Bm Dm im pm cm xm) (@freyd_homology_model_short_exact_row R M A0 B0 D0 i0 p0
  c0 x0) (@freyd_homology_model_short_exact_row R M A1 B1 D1 i1 p1 c1 x1) (@freyd_homology_model_short_exact_row R M A2 B2
  D2 i2 p2 c2 x2) (@freyd_raw_chain_map_generic R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm cm c0 fm)
  (@freyd_raw_chain_map_generic R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0 c0 c1 gm) (@freyd_raw_chain_map_generic R A1 B1 D1
  A2 B2 D2 i1 p1 i2 p2 a1 b1 d1 c1 c2 jm) (@freyd_raw_chain_zero_path R Bm B0 B1 bm b0 upper) (@freyd_raw_chain_zero_path R
  B0 B1 B2 b0 b1 lower) (@freyd_homology_model_record R M Dm D0 D1 dm d0 source_chain) (@freyd_homology_model_record R M A0
  A1 A2 a0 a1 target_chain);

/* Complete-arrow observation of the direct model component. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_maps;

symbol freyd_homology_model_connecting_observation [R : τ CommRing]
  (M : τ (FreydHomologyModel R))
  (N : τ (@FreydHomologyModelNormality R M))
  [Am : τ (@CommRingPresentation R)]
  [Bm : τ (@CommRingPresentation R)]
  [Dm : τ (@CommRingPresentation R)]
  [A0 : τ (@CommRingPresentation R)]
  [B0 : τ (@CommRingPresentation R)]
  [D0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [D1 : τ (@CommRingPresentation R)]
  [A2 : τ (@CommRingPresentation R)]
  [B2 : τ (@CommRingPresentation R)]
  [D2 : τ (@CommRingPresentation R)]
  (im : τ (@CommRingPresentationMorphism R Am Bm))
  (pm : τ (@CommRingPresentationMorphism R Bm Dm))
  (cm : τ (@CommRingFreydChainPair R Am Bm Dm im pm))
  (xm : τ (@FreydHomologyModelShortExact R M Am Bm Dm im pm cm))
  (i0 : τ (@CommRingPresentationMorphism R A0 B0))
  (p0 : τ (@CommRingPresentationMorphism R B0 D0))
  (c0 : τ (@CommRingFreydChainPair R A0 B0 D0 i0 p0))
  (x0 : τ (@FreydHomologyModelShortExact R M A0 B0 D0 i0 p0 c0))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 D1))
  (c1 : τ (@CommRingFreydChainPair R A1 B1 D1 i1 p1))
  (x1 : τ (@FreydHomologyModelShortExact R M A1 B1 D1 i1 p1 c1))
  (i2 : τ (@CommRingPresentationMorphism R A2 B2))
  (p2 : τ (@CommRingPresentationMorphism R B2 D2))
  (c2 : τ (@CommRingFreydChainPair R A2 B2 D2 i2 p2))
  (x2 : τ (@FreydHomologyModelShortExact R M A2 B2 D2 i2 p2 c2))
  (am : τ (@CommRingPresentationMorphism R Am A0))
  (bm : τ (@CommRingPresentationMorphism R Bm B0))
  (dm : τ (@CommRingPresentationMorphism R Dm D0))
  (fm : τ (@CommRingFreydHomologyChainMap R Am Bm Dm A0 B0 D0 im pm i0 p0 am bm dm))
  (a0 : τ (@CommRingPresentationMorphism R A0 A1))
  (b0 : τ (@CommRingPresentationMorphism R B0 B1))
  (d0 : τ (@CommRingPresentationMorphism R D0 D1))
  (gm : τ (@CommRingFreydHomologyChainMap R A0 B0 D0 A1 B1 D1 i0 p0 i1 p1 a0 b0 d0))
  (a1 : τ (@CommRingPresentationMorphism R A1 A2))
  (b1 : τ (@CommRingPresentationMorphism R B1 B2))
  (d1 : τ (@CommRingPresentationMorphism R D1 D2))
  (jm : τ (@CommRingFreydHomologyChainMap R A1 B1 D1 A2 B2 D2 i1 p1 i2 p2 a1 b1 d1))
  (upper : τ (@CommRingFreydChainPair R Bm B0 B1 bm b0))
  (lower : τ (@CommRingFreydChainPair R B0 B1 B2 b0 b1))
  (source_chain : τ (@CommRingFreydChainPair R Dm D0 D1 dm d0))
  (target_chain : τ (@CommRingFreydChainPair R A0 A1 A2 a0 a1))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) (@freyd_homology_model_object R M Dm D0 D1 dm d0 source_chain)
  (@freyd_homology_model_object R M A0 A1 A2 a0 a1 target_chain)
    (@freyd_homology_model_connecting R M N Am Bm Dm A0 B0 D0 A1 B1 D1 A2 B2 D2 im pm cm xm i0 p0 c0 x0 i1 p1 c1 x1 i2 p2 c2
      x2 am bm dm fm a0 b0 d0 gm a1 b1 d1 jm upper lower source_chain target_chain);
