/*
  Direct ordinary-sieve Grothendieck topologies.

  This one-way standard-library module builds on ordinary sieves without
  declaring an `Omega` family, a sheafification modality, or a generated
  coverage saturation.  A topology is an object-indexed proposition-valued
  predicate on ordinary sieves together with maximality, pullback stability,
  and local character.

  The Nat prerequisite is imported only for its reusable elementary
  `Unit_grpd` proposition witness.  It supplies the literal true proposition
  used by the maximal sieve and the checked chaotic-topology model.
*/

require open emdash.emdash3_2_sieves;
require open emdash.emdash3_2_nat_arithmetic;

/*
  Arrow observations and ordinary-sieve membership.

  An object of `Into_restr_cat(U)` is the dependent pair `(V,f)` with
  `f : Hom_K(V,U)`.  Membership in an ordinary sieve is the object classifier
  of its subterminal value at that pair.
*/
symbol into_restr_domain
  [K : Cat]
  [U : τ (Obj K)]
  (f : τ (Obj (@Into_restr_cat K U)))
  : τ (Obj K)
≔ sigma_Fst f;

symbol into_restr_arrow
  [K : Cat]
  [U : τ (Obj K)]
  (f : τ (Obj (@Into_restr_cat K U)))
  : τ (Hom K (@into_restr_domain K U f) U)
≔ sigma_Snd f;

symbol SieveMembership
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (f : τ (Obj (@Into_restr_cat K U)))
  : Grpd
≔ Obj
    (@Fibre_cat
      (@Into_restr_cat K U)
      (@sieve_higher K U R)
      f);

// Membership is proposition-valued by the ordinary-sieve witness at f.
symbol sieve_membership_is_prop
  [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (f : τ (Obj (@Into_restr_cat K U)))
  : τ (IsPropGrpd (@SieveMembership K U R f))
≔ @is_subterminal_cat_obj_prop
    (@Fibre_cat
      (@Into_restr_cat K U)
      (@sieve_higher K U R)
      f)
    ((@sieve_subterminal K U R) f);

/*
  Maximal ordinary sieve.

  The constant literal path category on Unit is a canonical subterminal true
  value.  This avoids asserting a definitional equality between
  `Terminal_cat` and `Path_cat(Unit_grpd)`.  Pullback computes through the
  existing constant-family rule.
*/
symbol truth_prop : τ PropU_grpd
≔ @Struct_trunc_grpd trunc_minus_one Unit_grpd unit_is_prop;

symbol maximal_sieve
  [K : Cat]
  (U : τ (Obj K))
  : τ (@Sieve K U)
≔ @sieve_intro
    K U
    (@Const_catd (@Into_restr_cat K U) (Path_cat Unit_grpd))
    (λ _ : τ (Obj (@Into_restr_cat K U)),
      @path_cat_is_subterminal Unit_grpd unit_is_prop);

/*
  Proposition-valued sieve coverage.

  `SieveCoverage(K)` is only a first-class object-indexed predicate.  The
  three laws below distinguish a Grothendieck topology from an arbitrary
  predicate.  Generating cover families and their free saturation are a
  separate later presentation.
*/
symbol SieveCoverage (K : Cat) : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Function_grpd (@Sieve K U) PropU_grpd);

symbol Covers
  [K : Cat]
  (J : τ (@SieveCoverage K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : Grpd
≔ @trunc_grpd_carrier trunc_minus_one (J U R);

symbol covers_is_prop
  [K : Cat]
  (J : τ (@SieveCoverage K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : τ (IsPropGrpd (@Covers K J U R))
≔ @trunc_grpd_evidence trunc_minus_one (J U R);

// The maximal sieve covers every object.
symbol GrothMaximal
  [K : Cat]
  (J : τ (@SieveCoverage K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K), @Covers K J U (@maximal_sieve K U));

// Covering sieves are stable under pullback along every base arrow.
symbol GrothStable
  [K : Cat]
  (J : τ (@SieveCoverage K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (Obj K)
        (λ V : τ (Obj K),
          @Pi_grpd
            (Hom K V U)
            (λ p : τ (Hom K V U),
              @Pi_grpd
                (@Sieve K U)
                (λ R : τ (@Sieve K U),
                  @Function_grpd
                    (@Covers K J U R)
                    (@Covers K J V
                      (@sieve_pullback K V U p R))))));

/*
  Local-character premise.

  For every `(V,f)` belonging to R, the pullback `f^*S` covers V.  The
  membership premise is proposition-valued by `sieve_membership_is_prop`; no
  Boolean or object-level membership test is added.
*/
symbol SieveLocalityPremise
  [K : Cat]
  (J : τ (@SieveCoverage K))
  [U : τ (Obj K)]
  (R S : τ (@Sieve K U))
  : Grpd
≔ @Pi_grpd
    (Obj (@Into_restr_cat K U))
    (λ f : τ (Obj (@Into_restr_cat K U)),
      @Function_grpd
        (@SieveMembership K U R f)
        (@Covers
          K J
          (@into_restr_domain K U f)
          (@sieve_pullback
            K
            (@into_restr_domain K U f)
            U
            (@into_restr_arrow K U f)
            S)));

// Covering R plus the locality premise for S implies that S covers.
symbol GrothLocal
  [K : Cat]
  (J : τ (@SieveCoverage K))
  : Grpd
≔ @Pi_grpd
    (Obj K)
    (λ U : τ (Obj K),
      @Pi_grpd
        (@Sieve K U)
        (λ R : τ (@Sieve K U),
          @Pi_grpd
            (@Sieve K U)
            (λ S : τ (@Sieve K U),
              @Function_grpd
                (@Covers K J U R)
                (@Function_grpd
                  (@SieveLocalityPremise K J U R S)
                  (@Covers K J U S)))));

// The three Grothendieck-topology laws for a selected sieve coverage.
symbol IsGrothTopology
  [K : Cat]
  (J : τ (@SieveCoverage K))
  : Grpd
≔ @Product_grpd
    (@GrothMaximal K J)
    (@Product_grpd (@GrothStable K J) (@GrothLocal K J));

// Evidence-retaining package of a coverage predicate and its three laws.
symbol GrothTopology (K : Cat) : Grpd
≔ `Σ_ J : τ (@SieveCoverage K), @IsGrothTopology K J;

symbol groth_topology_intro
  [K : Cat]
  (J : τ (@SieveCoverage K))
  (laws : τ (@IsGrothTopology K J))
  : τ (@GrothTopology K)
≔ @Struct_sigma
    (@SieveCoverage K)
    (λ P : τ (@SieveCoverage K), @IsGrothTopology K P)
    J
    laws;

symbol groth_topology_cover_predicate
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@SieveCoverage K)
≔ sigma_Fst T;

symbol groth_topology_laws
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@IsGrothTopology K (@groth_topology_cover_predicate K T))
≔ sigma_Snd T;

symbol groth_topology_maximal
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@GrothMaximal K (@groth_topology_cover_predicate K T))
≔ sigma_Fst (@groth_topology_laws K T);

symbol groth_topology_pullback
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@GrothStable K (@groth_topology_cover_predicate K T))
≔ sigma_Fst (sigma_Snd (@groth_topology_laws K T));

symbol groth_topology_local_character
  [K : Cat]
  (T : τ (@GrothTopology K))
  : τ (@GrothLocal K (@groth_topology_cover_predicate K T))
≔ sigma_Snd (sigma_Snd (@groth_topology_laws K T));

symbol groth_topology_covers
  [K : Cat]
  (T : τ (@GrothTopology K))
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  : Grpd
≔ @Covers K (@groth_topology_cover_predicate K T) U R;

/*
  Checked direct model: the chaotic topology.

  Every sieve covers, so maximality, pullback stability, and local character
  reduce to the unique Unit witness.  This is a concrete direct topology, not
  a claim that an arbitrary family coverage has already been freely saturated.
*/
symbol chaotic_sieve_coverage
  (K : Cat)
  : τ (@SieveCoverage K)
≔ λ U : τ (Obj K), λ _ : τ (@Sieve K U), truth_prop;

symbol chaotic_groth_topology_laws
  (K : Cat)
  : τ (@IsGrothTopology K (@chaotic_sieve_coverage K))
≔ @Product_pair_grpd
    (@GrothMaximal K (@chaotic_sieve_coverage K))
    (@Product_grpd
      (@GrothStable K (@chaotic_sieve_coverage K))
      (@GrothLocal K (@chaotic_sieve_coverage K)))
    (λ _ : τ (Obj K), tt)
    (@Product_pair_grpd
      (@GrothStable K (@chaotic_sieve_coverage K))
      (@GrothLocal K (@chaotic_sieve_coverage K))
      (λ U : τ (Obj K),
        λ V : τ (Obj K),
        λ p : τ (Hom K V U),
        λ R : τ (@Sieve K U),
        λ _ : τ (@Covers
          K (@chaotic_sieve_coverage K) U R),
        tt)
      (λ U : τ (Obj K),
        λ R : τ (@Sieve K U),
        λ S : τ (@Sieve K U),
        λ _ : τ (@Covers
          K (@chaotic_sieve_coverage K) U R),
        λ _ : τ (@SieveLocalityPremise
          K (@chaotic_sieve_coverage K) U R S),
        tt));

symbol chaotic_groth_topology
  (K : Cat)
  : τ (@GrothTopology K)
≔ @groth_topology_intro
    K
    (@chaotic_sieve_coverage K)
    (@chaotic_groth_topology_laws K);
