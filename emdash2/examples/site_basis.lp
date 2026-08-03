/*
  Reviewer for whole supplied sheaf restriction and basis equivalence.

  Presheaf restriction computes by ordinary opposite precomposition.  The
  selected sheaf restriction is related to that operation by one whole
  IsoEvidence, and comparison-lemma strength is one whole
  OmegaEquivAlong Cat_cat.  No component naturality or commutative-square
  family is supplied.
*/

require open emdash.emdash3_2_site_basis;

// Generic presheaf restriction is whole precomposition at the functor owner.
assert [A B V : Cat]
  (i : τ (Functor A B))
  (P : τ (Functor (Op_cat B) V)) ⊢
  @fapp0
    (@Functor_cat (Op_cat B) V)
    (@Functor_cat (Op_cat A) V)
    (@psh_restriction_func A B V i)
    P
  : τ (Functor (Op_cat A) V);

// The runtime cut-owner view compares proof-time with direct composition.
assert [A B V : Cat]
  (i : τ (Functor A B))
  (P : τ (Functor (Op_cat B) V)) ⊢
  @psh_restriction_value_path A B V i P
  : τ (@=
      (Obj (@Functor_cat (Op_cat A) V))
      (@fapp0
        (@Functor_cat (Op_cat B) V)
        (@Functor_cat (Op_cat A) V)
        (@psh_restriction_func A B V i)
        P)
      (@comp_cat_fapp0
        (Op_cat A)
        (Op_cat B)
        V
        P
        (@Op_func A B i)));

assert [A B V : Cat]
  (i : τ (Functor A B))
  (P : τ (Functor (Op_cat B) V)) ⊢
  @psh_restriction_value_iso A B V i P
  : τ (@IsoEvidence
      (@Functor_cat (Op_cat A) V)
      (@fapp0
        (@Functor_cat (Op_cat B) V)
        (@Functor_cat (Op_cat A) V)
        (@psh_restriction_func A B V i)
        P)
      (@comp_cat_fapp0
        (Op_cat A)
        (Op_cat B)
        V
        P
        (@Op_func A B i)));

// The first projection is a whole sheaf-restriction functor.
assert [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  (SA : τ (@SheafificationCapability A TA V))
  (SB : τ (@SheafificationCapability B TB V))
  (i : τ (Functor A B))
  (P : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i)) ⊢
  @supplied_sheaf_restriction_func A B V TA TB SA SB i P
  : τ (Functor (@Sheaf_cat B TB V) (@Sheaf_cat A TA V));

// The second projection compares whole composite functors.
assert [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  (SA : τ (@SheafificationCapability A TA V))
  (SB : τ (@SheafificationCapability B TB V))
  (i : τ (Functor A B))
  (P : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i)) ⊢
  @supplied_sheaf_restriction_underlying_iso A B V TA TB SA SB i P
  : τ (@IsoEvidence
      (@Functor_cat
        (@Sheaf_cat B TB V)
        (@Functor_cat (Op_cat A) V))
      (@comp_cat_fapp0
        (@Sheaf_cat B TB V)
        (@Sheaf_cat A TA V)
        (@Functor_cat (Op_cat A) V)
        (@sheaf_include_func A TA V SA)
        (@supplied_sheaf_restriction_func A B V TA TB SA SB i P))
      (@comp_cat_fapp0
        (@Sheaf_cat B TB V)
        (@Functor_cat (Op_cat B) V)
        (@Functor_cat (Op_cat A) V)
        (@psh_restriction_func A B V i)
        (@sheaf_include_func B TB V SB)));

// Basis semantics retain that exact restriction package.
assert [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  (SA : τ (@SheafificationCapability A TA V))
  (SB : τ (@SheafificationCapability B TB V))
  (i : τ (Functor A B))
  (Q : τ (@SuppliedSheafBasisEquivalenceAlong A B V TA TB SA SB i)) ⊢
  @supplied_sheaf_basis_restriction A B V TA TB SA SB i Q
  : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i);

// Its comparison is a whole fixed-functor category equivalence.
assert [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  (SA : τ (@SheafificationCapability A TA V))
  (SB : τ (@SheafificationCapability B TB V))
  (i : τ (Functor A B))
  (Q : τ (@SuppliedSheafBasisEquivalenceAlong A B V TA TB SA SB i)) ⊢
  @supplied_sheaf_basis_equivalence A B V TA TB SA SB i Q
  : τ (@OmegaEquivAlong
      Cat_cat
      (@Sheaf_cat B TB V)
      (@Sheaf_cat A TA V)
      (@supplied_sheaf_restriction_func
        A B V TA TB SA SB i
        (@supplied_sheaf_basis_restriction A B V TA TB SA SB i Q)));
