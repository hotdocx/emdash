/*
  Topology-local computational presentations of local CommRing sheaves.

  For a CommRing-valued presheaf O on a site (K,T), local nontriviality says
  that a stage where zero is invertible is covered by the empty sieve.  Local
  unit splitting says that, whenever s+t is invertible at U, one can select a
  covering sieve R on U and, for every retained member of R, select a Boolean
  branch witnessing that the restriction of s or of t is invertible.

  This witness-rich interface is the computational Kripke--Joyal form of the
  two nonautomatic support laws D(0)=bottom and
  D(s+t)<=D(s) join D(t).  It deliberately constructs neither a raw union of
  sieves nor a propositional truncation: the selected cover and branch remain
  executable presentation data.  The automatic laws for one and products,
  the comparison with a distributive lattice of opens, and the theorem
  relating this criterion to local stalk rings remain separate mathematical
  layers.

  When O is the included presheaf of a reflective ringed site, its supplied
  sheaf boundary is owned by that existing package.  This transparent module
  adds no rule or unifier and does not itself assert sheafhood, affineness, an
  open immersion, a scheme, or a category of schemes.
*/

require open emdash.emdash3_2_commutative_algebra_presheaves;
require open emdash.emdash3_2_sites;

// Literal bottom ordinary sieve, with Empty-valued membership at every arrow.
symbol empty_sieve
  [K : Cat]
  (U : τ (Obj K))
  : τ (@Sieve K U)
≔ @sieve_intro
    K U
    (@Const_catd (@Into_restr_cat K U) (Path_cat Empty_grpd))
    (λ _ : τ (Obj (@Into_restr_cat K U)),
      @path_cat_is_subterminal Empty_grpd empty_is_prop);

// Elimination from membership in the literal empty sieve.
symbol empty_sieve_member_elim
  [K : Cat]
  [U : τ (Obj K)]
  (q : τ (Obj (@Into_restr_cat K U)))
  (member : τ (@SieveMembership K U (@empty_sieve K U) q))
  (A : Grpd)
  : τ A
≔ @empty_elim (λ _ : τ Empty_grpd, A) member;

/*
  One executable local disjunction.

  The false branch retains unit evidence for s|q and the true branch retains
  unit evidence for t|q.  The Sigma is intentionally not truncated: a
  computational presentation may expose which branch was selected.
*/
symbol CommRingPshLocalUnitBranch
  [K : Cat]
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s t : τ (@CommRingPshSection K O U))
  (q : τ (Obj (@Into_restr_cat K U)))
  : Grpd
≔ `Σ_ side : τ Bool_grpd,
    @bool_elim
      (λ _ : τ Bool_grpd, Grpd_grpd)
      (@CommRingPshInvertibleAlong
        K O U s
        (@into_restr_domain K U q)
        (@into_restr_arrow K U q))
      (@CommRingPshInvertibleAlong
        K O U t
        (@into_restr_domain K U q)
        (@into_restr_arrow K U q))
      side;

symbol comm_ring_psh_local_unit_branch_left
  [K : Cat]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  [q : τ (Obj (@Into_restr_cat K U))]
  (unit_s : τ (@CommRingPshInvertibleAlong
      K O U s
      (@into_restr_domain K U q)
      (@into_restr_arrow K U q)))
  : τ (@CommRingPshLocalUnitBranch K O U s t q)
≔ @Struct_sigma
    Bool_grpd
    (λ side : τ Bool_grpd,
      @bool_elim
        (λ _ : τ Bool_grpd, Grpd_grpd)
        (@CommRingPshInvertibleAlong
          K O U s
          (@into_restr_domain K U q)
          (@into_restr_arrow K U q))
        (@CommRingPshInvertibleAlong
          K O U t
          (@into_restr_domain K U q)
          (@into_restr_arrow K U q))
        side)
    false unit_s;

symbol comm_ring_psh_local_unit_branch_right
  [K : Cat]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  [q : τ (Obj (@Into_restr_cat K U))]
  (unit_t : τ (@CommRingPshInvertibleAlong
      K O U t
      (@into_restr_domain K U q)
      (@into_restr_arrow K U q)))
  : τ (@CommRingPshLocalUnitBranch K O U s t q)
≔ @Struct_sigma
    Bool_grpd
    (λ side : τ Bool_grpd,
      @bool_elim
        (λ _ : τ Bool_grpd, Grpd_grpd)
        (@CommRingPshInvertibleAlong
          K O U s
          (@into_restr_domain K U q)
          (@into_restr_arrow K U q))
        (@CommRingPshInvertibleAlong
          K O U t
          (@into_restr_domain K U q)
          (@into_restr_arrow K U q))
        side)
    true unit_t;

symbol comm_ring_psh_local_unit_branch_side
  [K : Cat]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  [q : τ (Obj (@Into_restr_cat K U))]
  (branch : τ (@CommRingPshLocalUnitBranch K O U s t q))
  : τ Bool_grpd
≔ sigma_Fst branch;

symbol comm_ring_psh_local_unit_branch_evidence
  [K : Cat]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  [q : τ (Obj (@Into_restr_cat K U))]
  (branch : τ (@CommRingPshLocalUnitBranch K O U s t q))
  : τ (@bool_elim
      (λ _ : τ Bool_grpd, Grpd_grpd)
      (@CommRingPshInvertibleAlong
        K O U s
        (@into_restr_domain K U q)
        (@into_restr_arrow K U q))
      (@CommRingPshInvertibleAlong
        K O U t
        (@into_restr_domain K U q)
        (@into_restr_arrow K U q))
      (sigma_Fst branch))
≔ sigma_Snd branch;

/*
  A selected covering sieve subordinate to the local unit disjunction.

  The whole sieve supplies restriction closure.  A branch is requested only
  from an actual membership witness, so no Boolean membership decision or
  external naturality field is introduced.
*/
symbol CommRingPshLocalUnitCover
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  [U : τ (Obj K)]
  (s t : τ (@CommRingPshSection K O U))
  : Grpd
≔ `Σ_ R : τ (@Sieve K U),
   `Σ_ covers : τ (@groth_topology_covers K T U R),
      @Pi_grpd
        (Obj (@Into_restr_cat K U))
        (λ q : τ (Obj (@Into_restr_cat K U)),
          @Function_grpd
            (@SieveMembership K U R q)
            (@CommRingPshLocalUnitBranch K O U s t q));

symbol comm_ring_psh_local_unit_cover_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  (R : τ (@Sieve K U))
  (covers : τ (@groth_topology_covers K T U R))
  (branches : τ (@Pi_grpd
      (Obj (@Into_restr_cat K U))
      (λ q : τ (Obj (@Into_restr_cat K U)),
        @Function_grpd
          (@SieveMembership K U R q)
          (@CommRingPshLocalUnitBranch K O U s t q))))
  : τ (@CommRingPshLocalUnitCover K T O U s t)
≔ @Struct_sigma
    (@Sieve K U)
    (λ R0 : τ (@Sieve K U),
      `Σ_ covers0 : τ (@groth_topology_covers K T U R0),
        @Pi_grpd
          (Obj (@Into_restr_cat K U))
          (λ q : τ (Obj (@Into_restr_cat K U)),
            @Function_grpd
              (@SieveMembership K U R0 q)
              (@CommRingPshLocalUnitBranch K O U s t q)))
    R
    (@Struct_sigma
      (@groth_topology_covers K T U R)
      (λ _ : τ (@groth_topology_covers K T U R),
        @Pi_grpd
          (Obj (@Into_restr_cat K U))
          (λ q : τ (Obj (@Into_restr_cat K U)),
            @Function_grpd
              (@SieveMembership K U R q)
              (@CommRingPshLocalUnitBranch K O U s t q)))
      covers branches);

symbol comm_ring_psh_local_unit_cover_sieve
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  (C : τ (@CommRingPshLocalUnitCover K T O U s t))
  : τ (@Sieve K U)
≔ sigma_Fst C;

symbol comm_ring_psh_local_unit_cover_covers
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  (C : τ (@CommRingPshLocalUnitCover K T O U s t))
  : τ (@groth_topology_covers K T U (sigma_Fst C))
≔ sigma_Fst (sigma_Snd C);

symbol comm_ring_psh_local_unit_cover_branch_at
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  [U : τ (Obj K)]
  [s t : τ (@CommRingPshSection K O U)]
  (C : τ (@CommRingPshLocalUnitCover K T O U s t))
  (q : τ (Obj (@Into_restr_cat K U)))
  (member : τ (@SieveMembership K U (sigma_Fst C) q))
  : τ (@CommRingPshLocalUnitBranch K O U s t q)
≔ (sigma_Snd (sigma_Snd C)) q member;

// If zero is a unit at U, the literal empty sieve covers U.
symbol CommRingPshLocalNontriviality
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Function_grpd
        (@CommRingUnitEvidence
          (@comm_ring_psh_value K O U)
          (@comm_ring_zero (@comm_ring_psh_value K O U)))
        (@groth_topology_covers K T U (@empty_sieve K U)));

// A unit sum is locally split into an executable unit branch.
symbol CommRingPshLocalUnitSplitting
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (@CommRingPshSection K O U)
        (λ s : τ (@CommRingPshSection K O U),
          @Pi_grpd
            (@CommRingPshSection K O U)
            (λ t : τ (@CommRingPshSection K O U),
              @Function_grpd
                (@CommRingUnitEvidence
                  (@comm_ring_psh_value K O U)
                  (@comm_ring_add
                    (@comm_ring_psh_value K O U) s t))
                (@CommRingPshLocalUnitCover K T O U s t))));

// Selected computational presentation of a topology-local local ring object.
symbol CommRingPshTopologyLocalRingPresentation
  [K : Cat]
  (T : τ (@GrothTopology K))
  (O : τ (@CommRingPsh K))
  : Grpd
≔ `Σ_ zero_local : τ (@CommRingPshLocalNontriviality K T O),
      @CommRingPshLocalUnitSplitting K T O;

symbol comm_ring_psh_topology_local_ring_intro
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  (zero_local : τ (@CommRingPshLocalNontriviality K T O))
  (sum_local : τ (@CommRingPshLocalUnitSplitting K T O))
  : τ (@CommRingPshTopologyLocalRingPresentation K T O)
≔ @Struct_sigma
    (@CommRingPshLocalNontriviality K T O)
    (λ _ : τ (@CommRingPshLocalNontriviality K T O),
      @CommRingPshLocalUnitSplitting K T O)
    zero_local sum_local;

symbol comm_ring_psh_topology_local_ring_nontriviality
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  (L : τ (@CommRingPshTopologyLocalRingPresentation K T O))
  : τ (@CommRingPshLocalNontriviality K T O)
≔ sigma_Fst L;

symbol comm_ring_psh_topology_local_ring_unit_splitting
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  (L : τ (@CommRingPshTopologyLocalRingPresentation K T O))
  : τ (@CommRingPshLocalUnitSplitting K T O)
≔ sigma_Snd L;

// Execute local nontriviality at one stage.
symbol comm_ring_psh_topology_local_ring_empty_covers
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  (L : τ (@CommRingPshTopologyLocalRingPresentation K T O))
  (U : τ (Obj K))
  (zero_unit : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O U)
      (@comm_ring_zero (@comm_ring_psh_value K O U))))
  : τ (@groth_topology_covers K T U (@empty_sieve K U))
≔ (sigma_Fst L) U zero_unit;

// Execute local unit splitting at one stage and one unit sum.
symbol comm_ring_psh_topology_local_ring_split
  [K : Cat]
  [T : τ (@GrothTopology K)]
  [O : τ (@CommRingPsh K)]
  (L : τ (@CommRingPshTopologyLocalRingPresentation K T O))
  (U : τ (Obj K))
  (s t : τ (@CommRingPshSection K O U))
  (sum_unit : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O U)
      (@comm_ring_add (@comm_ring_psh_value K O U) s t)))
  : τ (@CommRingPshLocalUnitCover K T O U s t)
≔ (sigma_Snd L) U s t sum_unit;

/*
  Closed degeneracy model.

  In the chaotic topology the empty sieve covers every stage, so there is no
  retained branch to construct.  This proves that the presentation boundary
  is inhabited without claiming a nondegenerate geometric local-ring model.
*/
symbol chaotic_comm_ring_psh_local_nontriviality
  [K : Cat]
  (O : τ (@CommRingPsh K))
  : τ (@CommRingPshLocalNontriviality
      K (@chaotic_groth_topology K) O)
≔ λ U : τ (Obj K),
   λ _ : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O U)
      (@comm_ring_zero (@comm_ring_psh_value K O U))),
   tt;

symbol chaotic_comm_ring_psh_local_unit_splitting
  [K : Cat]
  (O : τ (@CommRingPsh K))
  : τ (@CommRingPshLocalUnitSplitting
      K (@chaotic_groth_topology K) O)
≔ λ U : τ (Obj K),
   λ s : τ (@CommRingPshSection K O U),
   λ t : τ (@CommRingPshSection K O U),
   λ _ : τ (@CommRingUnitEvidence
      (@comm_ring_psh_value K O U)
      (@comm_ring_add (@comm_ring_psh_value K O U) s t)),
   @comm_ring_psh_local_unit_cover_intro
      K (@chaotic_groth_topology K) O U s t
      (@empty_sieve K U)
      tt
      (λ q : τ (Obj (@Into_restr_cat K U)),
       λ member : τ (@SieveMembership K U (@empty_sieve K U) q),
         @empty_sieve_member_elim
           K U q member
           (@CommRingPshLocalUnitBranch K O U s t q));

symbol chaotic_comm_ring_psh_topology_local_ring
  [K : Cat]
  (O : τ (@CommRingPsh K))
  : τ (@CommRingPshTopologyLocalRingPresentation
      K (@chaotic_groth_topology K) O)
≔ @comm_ring_psh_topology_local_ring_intro
    K (@chaotic_groth_topology K) O
    (@chaotic_comm_ring_psh_local_nontriviality K O)
    (@chaotic_comm_ring_psh_local_unit_splitting K O);
