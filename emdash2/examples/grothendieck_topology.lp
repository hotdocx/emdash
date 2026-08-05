/*
  Reviewer-facing PSSS-04a example: direct ordinary-sieve Grothendieck
  topologies without an `Omega` family or generated coverage saturation.
*/

require open emdash.emdash3_2_sites;

// Objects of the restriction total expose their domain and arrow.
assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @into_restr_domain K U (Struct_sigma V p)
  ≡ V;

assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @into_restr_arrow K U (Struct_sigma V p)
  ≡ p;

// Membership in an ordinary sieve is proposition-valued.
assert [K : Cat] (U : τ (Obj K))
  (R : τ (@Sieve K U))
  (f : τ (Obj (@Into_restr_cat K U))) ⊢
  @sieve_membership_is_prop K U R f
  : τ (IsPropGrpd (@SieveMembership K U R f));

// The maximal ordinary sieve is pointwise true and stable under pullback.
assert [K : Cat] (U : τ (Obj K))
  (f : τ (Obj (@Into_restr_cat K U))) ⊢
  @SieveMembership K U (@maximal_sieve K U) f
  ≡ Unit_grpd;

assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U)) ⊢
  @sieve_pullback K V U p (@maximal_sieve K U)
  ≡ @maximal_sieve K V;

// Its literal Path(Unit) value is not identified with Terminal_cat.
assertnot [K : Cat] (U : τ (Obj K)) ⊢
  @sieve_higher K U (@maximal_sieve K U)
  ≡ @maximal_higher_sieve K U;

// Every selected covering predicate decodes to a proposition.
assert [K : Cat]
  (J : τ (@SieveCoverage K))
  (U : τ (Obj K))
  (R : τ (@Sieve K U)) ⊢
  @covers_is_prop K J U R
  : τ (IsPropGrpd (@Covers K J U R));

// Every sieve covers in the chaotic topology.
assert [K : Cat] (U : τ (Obj K))
  (R : τ (@Sieve K U)) ⊢
  @groth_topology_covers K (@chaotic_groth_topology K) U R
  ≡ Unit_grpd;

// Its pullback-stability law computes to the unique truth witness.
assert [K : Cat] (V U : τ (Obj K))
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U)) ⊢
  (@groth_topology_pullback K (@chaotic_groth_topology K))
    U V p R tt
  ≡ tt;

// Local character is wired through membership and sieve pullback.
assert [K : Cat] (U : τ (Obj K))
  (R S : τ (@Sieve K U)) ⊢
  (@groth_topology_local_character K (@chaotic_groth_topology K))
    U R S tt
    (λ f : τ (Obj (@Into_restr_cat K U)),
      λ _ : τ (@SieveMembership K U R f),
      tt)
  ≡ tt;

assert [K : Cat] ⊢
  @chaotic_groth_topology K
  : τ (@GrothTopology K);

// Small direct combinatorial instance.
assert ⊢
  @chaotic_groth_topology Terminal_cat
  : τ (@GrothTopology Terminal_cat);
