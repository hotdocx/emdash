/*
  Supplied whole restriction and basis equivalence between sheaf theories.

  Precomposition with the opposite of i:A->B gives whole restriction of
  V-valued presheaves.  A supplied sheaf restriction is tied to that
  computing operation by one IsoEvidence between whole composite functors.
  Comparison-lemma strength is then retained separately as an
  OmegaEquivAlong Cat_cat for the selected restriction functor.

  Naturality and arrow action remain at the generic functor, transformation,
  IsoEvidence, and OmegaEquivAlong owners.  Local exactness may justify a
  comparison semantically, but no local-exactness derivation or component
  commutative-square family is stored here.

  This transparent rule-free module does not construct a topology,
  sheafification, continuity/cocontinuity, an induced slice site, a
  sheafification Beck--Chevalley mate, or a raw equivalence of base
  categories.
*/

require open emdash.emdash3_2_ringed_sites;

// Whole restriction of V-valued presheaves along i:A->B.
symbol psh_restriction_func
  [A B V : Cat]
  (i : τ (Functor A B))
  : τ (Functor
      (@Functor_cat (Op_cat B) V)
      (@Functor_cat (Op_cat A) V))
≔ @comp_cat_con_func
    (Op_cat A)
    (Op_cat B)
    V
    (@Op_func A B i);

/*
  Proof-time bridge from the generic precomposition object's stable cut-owner
  normal form to the direct composition spelling.  This is intentionally an
  equality path, not a runtime fold: generic precomposition keeps its existing
  whole arrow action, while concrete consumers may compare with a computing
  direct-composition presentation.
*/
symbol psh_restriction_value_path
  [A B V : Cat]
  (i : τ (Functor A B))
  (P : τ (Functor (Op_cat B) V))
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
        (@Op_func A B i)))
≔ @eq_refl
    (Obj (@Functor_cat (Op_cat A) V))
    (@fapp0
      (@Functor_cat (Op_cat B) V)
      (@Functor_cat (Op_cat A) V)
      (@psh_restriction_func A B V i)
      P);

// The same proof-time presentation bridge as ordinary isomorphism evidence.
symbol psh_restriction_value_iso
  [A B V : Cat]
  (i : τ (Functor A B))
  (P : τ (Functor (Op_cat B) V))
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
        (@Op_func A B i)))
≔ @idtoiso_cat
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
      (@Op_func A B i))
    (@psh_restriction_value_path A B V i P);

/*
  Supplied sheaf restriction along i and one whole natural isomorphism saying
  that inclusion exposes ordinary presheaf restriction.
*/
symbol SuppliedSheafRestrictionAlong
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  (SA : τ (@SheafificationCapability A TA V))
  (SB : τ (@SheafificationCapability B TB V))
  (i : τ (Functor A B))
  : Grpd
≔ `Σ_ pull : τ (Functor
      (@Sheaf_cat B TB V)
      (@Sheaf_cat A TA V)),
    @IsoEvidence
      (@Functor_cat
        (@Sheaf_cat B TB V)
        (@Functor_cat (Op_cat A) V))
      (@comp_cat_fapp0
        (@Sheaf_cat B TB V)
        (@Sheaf_cat A TA V)
        (@Functor_cat (Op_cat A) V)
        (@sheaf_include_func A TA V SA)
        pull)
      (@comp_cat_fapp0
        (@Sheaf_cat B TB V)
        (@Functor_cat (Op_cat B) V)
        (@Functor_cat (Op_cat A) V)
        (@psh_restriction_func A B V i)
        (@sheaf_include_func B TB V SB));

symbol supplied_sheaf_restriction_intro
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  [SA : τ (@SheafificationCapability A TA V)]
  [SB : τ (@SheafificationCapability B TB V)]
  [i : τ (Functor A B)]
  (pull : τ (Functor
      (@Sheaf_cat B TB V)
      (@Sheaf_cat A TA V)))
  (underlying : τ (@IsoEvidence
      (@Functor_cat
        (@Sheaf_cat B TB V)
        (@Functor_cat (Op_cat A) V))
      (@comp_cat_fapp0
        (@Sheaf_cat B TB V)
        (@Sheaf_cat A TA V)
        (@Functor_cat (Op_cat A) V)
        (@sheaf_include_func A TA V SA)
        pull)
      (@comp_cat_fapp0
        (@Sheaf_cat B TB V)
        (@Functor_cat (Op_cat B) V)
        (@Functor_cat (Op_cat A) V)
        (@psh_restriction_func A B V i)
        (@sheaf_include_func B TB V SB))))
  : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i)
≔ @Struct_sigma
    (@Functor (@Sheaf_cat B TB V) (@Sheaf_cat A TA V))
    (λ pull0 : τ (Functor
        (@Sheaf_cat B TB V)
        (@Sheaf_cat A TA V)),
      @IsoEvidence
        (@Functor_cat
          (@Sheaf_cat B TB V)
          (@Functor_cat (Op_cat A) V))
        (@comp_cat_fapp0
          (@Sheaf_cat B TB V)
          (@Sheaf_cat A TA V)
          (@Functor_cat (Op_cat A) V)
          (@sheaf_include_func A TA V SA)
          pull0)
        (@comp_cat_fapp0
          (@Sheaf_cat B TB V)
          (@Functor_cat (Op_cat B) V)
          (@Functor_cat (Op_cat A) V)
          (@psh_restriction_func A B V i)
          (@sheaf_include_func B TB V SB)))
    pull underlying;

symbol supplied_sheaf_restriction_func
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  [SA : τ (@SheafificationCapability A TA V)]
  [SB : τ (@SheafificationCapability B TB V)]
  [i : τ (Functor A B)]
  (P : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i))
  : τ (Functor (@Sheaf_cat B TB V) (@Sheaf_cat A TA V))
≔ sigma_Fst P;

symbol supplied_sheaf_restriction_underlying_iso
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  [SA : τ (@SheafificationCapability A TA V)]
  [SB : τ (@SheafificationCapability B TB V)]
  [i : τ (Functor A B)]
  (P : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i))
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
        (@sheaf_include_func B TB V SB)))
≔ sigma_Snd P;

// Comparison-lemma strength: the selected restriction is a whole equivalence.
symbol SuppliedSheafBasisEquivalenceAlong
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  (SA : τ (@SheafificationCapability A TA V))
  (SB : τ (@SheafificationCapability B TB V))
  (i : τ (Functor A B))
  : Grpd
≔ `Σ_ P : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i),
    @OmegaEquivAlong
      Cat_cat
      (@Sheaf_cat B TB V)
      (@Sheaf_cat A TA V)
      (@supplied_sheaf_restriction_func A B V TA TB SA SB i P);

symbol supplied_sheaf_basis_intro
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  [SA : τ (@SheafificationCapability A TA V)]
  [SB : τ (@SheafificationCapability B TB V)]
  [i : τ (Functor A B)]
  (P : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i))
  (equiv : τ (@OmegaEquivAlong
      Cat_cat
      (@Sheaf_cat B TB V)
      (@Sheaf_cat A TA V)
      (@supplied_sheaf_restriction_func A B V TA TB SA SB i P)))
  : τ (@SuppliedSheafBasisEquivalenceAlong A B V TA TB SA SB i)
≔ @Struct_sigma
    (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i)
    (λ P0 : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i),
      @OmegaEquivAlong
        Cat_cat
        (@Sheaf_cat B TB V)
        (@Sheaf_cat A TA V)
        (@supplied_sheaf_restriction_func A B V TA TB SA SB i P0))
    P equiv;

symbol supplied_sheaf_basis_restriction
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  [SA : τ (@SheafificationCapability A TA V)]
  [SB : τ (@SheafificationCapability B TB V)]
  [i : τ (Functor A B)]
  (P : τ (@SuppliedSheafBasisEquivalenceAlong A B V TA TB SA SB i))
  : τ (@SuppliedSheafRestrictionAlong A B V TA TB SA SB i)
≔ sigma_Fst P;

symbol supplied_sheaf_basis_equivalence
  [A B V : Cat]
  [TA : τ (@GrothTopology A)]
  [TB : τ (@GrothTopology B)]
  [SA : τ (@SheafificationCapability A TA V)]
  [SB : τ (@SheafificationCapability B TB V)]
  [i : τ (Functor A B)]
  (P : τ (@SuppliedSheafBasisEquivalenceAlong A B V TA TB SA SB i))
  : τ (@OmegaEquivAlong
      Cat_cat
      (@Sheaf_cat B TB V)
      (@Sheaf_cat A TA V)
      (@supplied_sheaf_restriction_func
        A B V TA TB SA SB i
        (@supplied_sheaf_basis_restriction A B V TA TB SA SB i P)))
≔ sigma_Snd P;
