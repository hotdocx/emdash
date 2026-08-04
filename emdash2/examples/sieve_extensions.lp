/*
  Reviewer for ordinary-sieve extension and topology-local presheaves.

  The extended sieve computes fibrewise as pairs `(f,member)`, and its whole
  inclusion into Yoneda computes to first projection.  The resulting locality
  predicate is a whole Hom equivalence, not external component descent data.
*/

require open emdash.emdash3_2_sieve_extensions;

// The extended sieve value is the generic fibrewise dependent sum.
assert [K : Cat]
  [U V : τ (Obj K)]
  (R : τ (@Sieve K U)) ⊢
  @Fibre_cat
    (Op_cat K)
    (@ordinary_sieve_extension_psh K U R)
    V
  ≡ @fibrewise_sigma_value_cat
      (Op_cat K)
      (@yoneda_psh K U)
      (@sieve_higher K U R)
      V;

// The extension inclusion is one whole presheaf arrow.
assert [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U)) ⊢
  @ordinary_sieve_extension_inclusion K U R
  : τ (Hom
      (@Psh_cat K)
      (@ordinary_sieve_extension_psh K U R)
      (@yoneda_psh K U));

// A retained member selects one whole Yoneda section of the extension.
assert [K : Cat]
  [V U : τ (Obj K)]
  (p : τ (Hom K V U))
  (R : τ (@Sieve K U))
  (member : τ (@SieveMembership K U R (Struct_sigma V p))) ⊢
  @ordinary_sieve_member_section K V U p R member
  : τ (Hom
      (@Psh_cat K)
      (@yoneda_psh K V)
      (@ordinary_sieve_extension_psh K U R));

// Its component is the literal first projection from pairs `(f,member)`.
assert [K : Cat]
  [U V : τ (Obj K)]
  (R : τ (@Sieve K U)) ⊢
  @tapp0_fapp0
    (Op_cat K)
    Cat_cat
    (@ordinary_sieve_extension_psh K U R)
    (@yoneda_psh K U)
    V
    (@ordinary_sieve_extension_inclusion K U R)
  ≡ @Sigma_proj1_func
      (@Fibre_cat (Op_cat K) (@yoneda_psh K U) V)
      (@fibrewise_sigma_fibre_catd
        (Op_cat K)
        (@yoneda_psh K U)
        (@sieve_higher K U R)
        V);

// At a literal pair, the whole component computes to its retained base arrow.
assert [K : Cat]
  [U V : τ (Obj K)]
  (R : τ (@Sieve K U))
  (f : τ (Obj (@Fibre_cat (Op_cat K) (@yoneda_psh K U) V)))
  (member : τ (Obj (@Fibre_cat
      (@Fibre_cat (Op_cat K) (@yoneda_psh K U) V)
      (@fibrewise_sigma_fibre_catd
        (Op_cat K)
        (@yoneda_psh K U)
        (@sieve_higher K U R)
        V)
      f))) ⊢
  @fapp0
    (@Fibre_cat
      (Op_cat K)
      (@ordinary_sieve_extension_psh K U R)
      V)
    (@Fibre_cat (Op_cat K) (@yoneda_psh K U) V)
    (@tapp0_fapp0
      (Op_cat K)
      Cat_cat
      (@ordinary_sieve_extension_psh K U R)
      (@yoneda_psh K U)
      V
      (@ordinary_sieve_extension_inclusion K U R))
    (Struct_sigma f member)
  ≡ f;

// Restriction along that exact inclusion is the fixed forward locality map.
assert [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (X : τ (@Psh K)) ⊢
  @ordinary_sieve_local_precomp K U R X
  : τ (Functor
      (Hom_cat (@Psh_cat K) (@yoneda_psh K U) X)
      (Hom_cat
        (@Psh_cat K)
        (@ordinary_sieve_extension_psh K U R)
        X));

// Locality at one sieve and at a whole topology are first-class classifiers.
assert [K : Cat]
  [U : τ (Obj K)]
  (R : τ (@Sieve K U))
  (X : τ (@Psh K)) ⊢
  @PshLocalAtOrdinarySieve K U R X
  : Grpd;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (X : τ (@Psh K)) ⊢
  @IsTopologyLocalPsh K T X
  : Grpd;
