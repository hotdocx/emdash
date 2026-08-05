/*
  Reviewer-facing supplied sheafification and reflective commutative-ringed
  sites.

  The supplied capability is a genuine reflector: it contains an adjunction
  and fixed-forward equivalence evidence for the actual counit at every sheaf.
  Glue is the whole internal adjunction mate, so its two cancellation laws are
  inherited from ProfComparison/DefIso.  The reflective ringed-site package
  exposes a CommRing-valued structure sheaf through the whole inclusion
  functor.

  These assertions construct no canonical sheafification, descent theorem,
  left-exactness proof, local-ring condition, affine atlas, or scheme.
*/

require open emdash.emdash3_2_ringed_sites;

// catalog-area: Supplied reflective sheafification and ringed sites
assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (include : τ (@Functor
      (@Sheaf_cat K T V)
      (@Functor_cat (Op_cat K) V)))
  (sheafify : τ (@Functor
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)))
  (adjunction : τ (@Adjunction
      (@Functor_cat (Op_cat K) V)
      (@Sheaf_cat K T V)
      sheafify
      include)) ⊢
  @sheaf_adjunction_intro K T V include sheafify adjunction
  : τ (@SheafAdjunctionData K T V);

assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (A : τ (@SheafAdjunctionData K T V))
  (reflects : τ (@IsSheafificationReflector K T V A)) ⊢
  @sheafification_capability_intro K T V A reflects
  : τ (@SheafificationCapability K T V);

// Reflection is fixed to the actual counit component, not a parallel arrow.
assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  (R : τ (Obj (@Sheaf_cat K T V))) ⊢
  @sheafification_counit_at K T V S R
  : τ (Hom
      (@Sheaf_cat K T V)
      (@fapp0
        (@Functor_cat (Op_cat K) V)
        (@Sheaf_cat K T V)
        (@sheafify_func K T V S)
        (@fapp0
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          R))
      R);

assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  (R : τ (Obj (@Sheaf_cat K T V))) ⊢
  (@sheafification_reflector K T V S) R
  : τ (@OmegaEquivAlong
      (@Sheaf_cat K T V)
      (@fapp0
        (@Functor_cat (Op_cat K) V)
        (@Sheaf_cat K T V)
        (@sheafify_func K T V S)
        (@fapp0
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          R))
      R
      (@sheafification_counit_at K T V S R));

// The mate is whole and polymorphic in both diagram shapes.
assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  [I J : Cat]
  (M : τ (@Functor I (@Functor_cat (Op_cat K) V)))
  (H : τ (@Functor J (@Sheaf_cat K T V))) ⊢
  @sheafification_mate K T V S I J M H
  : τ (ProfComparison
      (@Hom_prof_along
        I J
        (@Sheaf_cat K T V)
        (@comp_cat_fapp0
          I
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          (@sheafify_func K T V S)
          M)
        H)
      (@Hom_prof_along
        I J
        (@Functor_cat (Op_cat K) V)
        M
        (@comp_cat_fapp0
          J
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          H)));

// Glue followed by unglue recovers every incoming internal map.
assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  [I J : Cat]
  (M : τ (@Functor I (@Functor_cat (Op_cat K) V)))
  (H : τ (@Functor J (@Sheaf_cat K T V)))
  [P : τ (Prof I J)]
  (r : τ (ProfMap
      P
      (@Hom_prof_along
        I J
        (@Functor_cat (Op_cat K) V)
        M
        (@comp_cat_fapp0
          J
          (@Sheaf_cat K T V)
          (@Functor_cat (Op_cat K) V)
          (@sheaf_include_func K T V S)
          H)))) ⊢
  @sheafification_unglue K T V S I J M H P
    (@sheafification_glue K T V S I J M H P r)
  ≡ r;

// Unglue followed by glue recovers every sheaf-side internal map.
assert [K : Cat]
  [T : τ (@GrothTopology K)]
  [V : Cat]
  (S : τ (@SheafificationCapability K T V))
  [I J : Cat]
  (M : τ (@Functor I (@Functor_cat (Op_cat K) V)))
  (H : τ (@Functor J (@Sheaf_cat K T V)))
  [P : τ (Prof I J)]
  (r : τ (ProfMap
      P
      (@Hom_prof_along
        I J
        (@Sheaf_cat K T V)
        (@comp_cat_fapp0
          I
          (@Functor_cat (Op_cat K) V)
          (@Sheaf_cat K T V)
          (@sheafify_func K T V S)
          M)
        H))) ⊢
  @sheafification_glue K T V S I J M H P
    (@sheafification_unglue K T V S I J M H P r)
  ≡ r;

// A reflective ringed site consumes the CommRing-valued capability.
assert [K : Cat]
  (T : τ (@GrothTopology K))
  (S : τ (@SheafificationCapability K T CommRing_cat))
  (O : τ (Obj (@Sheaf_cat K T CommRing_cat))) ⊢
  @reflective_comm_ringed_site_intro K T S O
  : τ (@ReflectiveCommRingedSite K);

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (S : τ (@SheafificationCapability K T CommRing_cat))
  (O : τ (Obj (@Sheaf_cat K T CommRing_cat))) ⊢
  @reflective_comm_ringed_site_topology K
    (@reflective_comm_ringed_site_intro K T S O)
  ≡ T;

assert [K : Cat]
  (T : τ (@GrothTopology K))
  (S : τ (@SheafificationCapability K T CommRing_cat))
  (O : τ (Obj (@Sheaf_cat K T CommRing_cat))) ⊢
  @reflective_comm_ringed_site_structure_sheaf K
    (@reflective_comm_ringed_site_intro K T S O)
  ≡ O;

// The underlying structure is a whole CommRing-valued presheaf.
assert [K : Cat]
  (X : τ (@ReflectiveCommRingedSite K)) ⊢
  @reflective_comm_ringed_site_underlying_psh K X
  : τ (@CommRingPsh K);
