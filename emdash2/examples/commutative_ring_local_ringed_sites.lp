/*
  Reviewer for topology-local computational local-ring presentations.

  The selected cover and Boolean unit branch compute through transparent
  Sigma owners.  No raw sieve join, truncation, external restriction law, or
  scheme claim is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_local_ringed_sites;

// The bottom sieve is an ordinary sieve with literal Empty membership.
assert [K : Cat]
  (U : τ (Obj K)) ⊢
  @empty_sieve K U : τ (@Sieve K U);

assert [K : Cat]
  (U V : τ (Obj K))
  (f : τ (Hom K V U)) ⊢
  @SieveMembership
    K U (@empty_sieve K U)
    (@Struct_sigma
      (Obj K)
      (λ V0 : τ (Obj K), Hom K V0 U)
      V f)
  ≡ Empty_grpd;

// Both constructors expose an executable Boolean branch.
assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (q : τ (Obj (@Into_restr_cat K U)))
  (unit_s : τ (@CommRingPshInvertibleAlong
      K O U s
      (@into_restr_domain K U q)
      (@into_restr_arrow K U q))) ⊢
  @comm_ring_psh_local_unit_branch_side
    K O U s t q
    (@comm_ring_psh_local_unit_branch_left K O U s t q unit_s)
  ≡ false;

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (q : τ (Obj (@Into_restr_cat K U)))
  (unit_t : τ (@CommRingPshInvertibleAlong
      K O U t
      (@into_restr_domain K U q)
      (@into_restr_arrow K U q))) ⊢
  @comm_ring_psh_local_unit_branch_evidence
    K O U s t q
    (@comm_ring_psh_local_unit_branch_right K O U s t q unit_t)
  ≡ unit_t;

// The selected cover retains its original sieve, coverhood, and branches.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (branches : τ (@Pi_grpd
      (Obj (@Into_restr_cat K U))
      (λ q : τ (Obj (@Into_restr_cat K U)),
        @Function_grpd
          (@SieveMembership K U R q)
          (@CommRingPshLocalUnitBranch K O U s t q)))) ⊢
  @comm_ring_psh_local_unit_cover_sieve
    K T O U s t
    (@comm_ring_psh_local_unit_cover_intro
      K T O U s t R covers branches)
  ≡ R;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (branches : τ (@Pi_grpd
      (Obj (@Into_restr_cat K U))
      (λ q : τ (Obj (@Into_restr_cat K U)),
        @Function_grpd
          (@SieveMembership K U R q)
          (@CommRingPshLocalUnitBranch K O U s t q)))) ⊢
  @comm_ring_psh_local_unit_cover_covers
    K T O U s t
    (@comm_ring_psh_local_unit_cover_intro
      K T O U s t R covers branches)
  ≡ covers;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (branches : τ (@Pi_grpd
      (Obj (@Into_restr_cat K U))
      (λ q : τ (Obj (@Into_restr_cat K U)),
        @Function_grpd
          (@SieveMembership K U R q)
          (@CommRingPshLocalUnitBranch K O U s t q))))
  (q : τ (Obj (@Into_restr_cat K U)))
  (member : τ (@SieveMembership K U R q)) ⊢
  @comm_ring_psh_local_unit_cover_branch_at
    K T O U s t
    (@comm_ring_psh_local_unit_cover_intro
      K T O U s t R covers branches)
    q member
  ≡ branches q member;

// The local-ring package is transparent, and its executable eliminator
// returns the originally selected local cover.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (zero_local : τ (@CommRingPshLocalNontriviality K T O))
  (sum_local : τ (@CommRingPshLocalUnitSplitting K T O)) ⊢
  @comm_ring_psh_topology_local_ring_nontriviality
    K T O
    (@comm_ring_psh_topology_local_ring_intro
      K T O zero_local sum_local)
  ≡ zero_local;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  (zero_local : τ (@CommRingPshLocalNontriviality K T O))
  (sum_local : τ (@CommRingPshLocalUnitSplitting K T O))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (sum_unit : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O U)
      (@comm_ring_add (@comm_ring_psh_value K O U) s t))) ⊢
  @comm_ring_psh_topology_local_ring_split
    K T O
    (@comm_ring_psh_topology_local_ring_intro
      K T O zero_local sum_local)
    U s t sum_unit
  ≡ sum_local U s t sum_unit;

// The chaotic model is closed; its selected local cover is the empty sieve.
assert [K : Cat]
  (O : τ (@CommRingPsh K)) ⊢
  @chaotic_comm_ring_psh_topology_local_ring K O
  : τ (@CommRingPshTopologyLocalRingPresentation
      K (@chaotic_groth_topology K) O);

assert [K : Cat]
  (O : τ (@CommRingPsh K))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (sum_unit : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O U)
      (@comm_ring_add (@comm_ring_psh_value K O U) s t))) ⊢
  @comm_ring_psh_local_unit_cover_sieve
    K (@chaotic_groth_topology K) O U s t
    (@comm_ring_psh_topology_local_ring_split
      K (@chaotic_groth_topology K) O
      (@chaotic_comm_ring_psh_topology_local_ring K O)
      U s t sum_unit)
  ≡ @empty_sieve K U;
