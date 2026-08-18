/*
  Focused reviewer for the boundary and three horns of Delta[2].

  Membership is a computed Empty/Unit proposition obtained from omission bits
  on face codes. One whole higher-sieve owner retains generic restriction and
  naturality; existing ordinary-sieve pullback, extension, and inclusion own
  the surrounding categorical structure.
*/

require open emdash.emdash3_2_simplex2_sieves;

assert ⊢
  simplex_bool_is_set
  : τ (IsSetGrpd Bool_grpd);

// The identity three-vertex face lies in neither boundary nor any horn.
assert ⊢
  @Simplex2SieveMember
    simplex2_boundary_kind
    (succ (succ (succ zero)))
    (@face_identity (succ (succ (succ zero))))
  ≡ Empty_grpd;

assert ⊢
  @Simplex2SieveMember
    simplex2_horn_zero_kind
    (succ (succ (succ zero)))
    (@face_identity (succ (succ (succ zero))))
  ≡ Empty_grpd;

// Every codimension-one edge lies in the boundary.
assert ⊢
  @Simplex2SieveMember
    simplex2_boundary_kind
    (succ (succ zero))
    simplex_edge_zero_one_code
  ≡ Unit_grpd;

assert ⊢
  @Simplex2SieveMember
    simplex2_boundary_kind
    (succ (succ zero))
    simplex_edge_zero_two_code
  ≡ Unit_grpd;

assert ⊢
  @Simplex2SieveMember
    simplex2_boundary_kind
    (succ (succ zero))
    simplex_edge_one_two_code
  ≡ Unit_grpd;

// Edge ij is excluded exactly from the horn missing the opposite vertex.
assert ⊢
  @Simplex2SieveMember
    simplex2_horn_two_kind
    (succ (succ zero))
    simplex_edge_zero_one_code
  ≡ Empty_grpd;

assert ⊢
  @Simplex2SieveMember
    simplex2_horn_one_kind
    (succ (succ zero))
    simplex_edge_zero_two_code
  ≡ Empty_grpd;

assert ⊢
  @Simplex2SieveMember
    simplex2_horn_zero_kind
    (succ (succ zero))
    simplex_edge_one_two_code
  ≡ Empty_grpd;

// The other horn incidences compute to true.
assert ⊢
  @Simplex2SieveMember
    simplex2_horn_zero_kind
    (succ (succ zero))
    simplex_edge_zero_two_code
  ≡ Unit_grpd;

assert ⊢
  @Simplex2SieveMember
    simplex2_horn_two_kind
    (succ (succ zero))
    simplex_edge_one_two_code
  ≡ Unit_grpd;

// Public ordinary-sieve membership uses the same computed proposition.
assert ⊢
  @SieveMembership
    SemiDeltaPlus_cat
    (succ (succ (succ zero)))
    simplex2_horn_two_sieve
    (Struct_sigma (succ (succ zero)) simplex_edge_zero_one_code)
  ≡ Empty_grpd;

assert ⊢
  @SieveMembership
    SemiDeltaPlus_cat
    (succ (succ (succ zero)))
    simplex2_boundary_sieve
    (Struct_sigma (succ (succ zero)) simplex_edge_zero_one_code)
  ≡ Unit_grpd;

// Every selected fibre is proposition-valued and therefore subterminal.
assert
  (kind : τ Simplex2SieveKind)
  [p : τ Nat_grpd]
  (f : τ (@FaceCode p (succ (succ (succ zero))))) ⊢
  @simplex2_sieve_member_is_prop kind p f
  : τ (IsPropGrpd (@Simplex2SieveMember kind p f));

// One next action remains at the generic whole Catd owner.
assert
  (kind : τ Simplex2SieveKind)
  (q r : τ (Obj (@Into_restr_cat
      SemiDeltaPlus_cat (succ (succ (succ zero)))))) ⊢
  @fapp1_func
    (@Into_restr_cat
      SemiDeltaPlus_cat (succ (succ (succ zero))))
    Cat_cat
    (@simplex2_higher_sieve kind)
    q r
  : τ (Functor
      (Hom_cat
        (@Into_restr_cat
          SemiDeltaPlus_cat (succ (succ (succ zero))))
        q r)
      (Functor_cat
        (@Fibre_cat
          (@Into_restr_cat
            SemiDeltaPlus_cat (succ (succ (succ zero))))
          (@simplex2_higher_sieve kind)
          q)
        (@Fibre_cat
          (@Into_restr_cat
            SemiDeltaPlus_cat (succ (succ (succ zero))))
          (@simplex2_higher_sieve kind)
          r)));

// Generic pullback computes at the canonical represented postcomposition.
assert
  (kind : τ Simplex2SieveKind)
  [q p : τ Nat_grpd]
  (r : τ (@FaceCode q (succ (succ (succ zero)))))
  (g : τ (@FaceCode p q)) ⊢
  @SieveMembership
    SemiDeltaPlus_cat q
    (@simplex2_sieve_pullback kind q r)
    (Struct_sigma p g)
  ≡ @SieveMembership
      SemiDeltaPlus_cat
      (succ (succ (succ zero)))
      (@simplex2_sieve kind)
      (@into_restr_postcompose
        SemiDeltaPlus_cat q (succ (succ (succ zero))) r
        (Struct_sigma p g));

// At structural face-code normal form, precomposition preserves the result.
assert ⊢
  @Simplex2SieveMember
    simplex2_boundary_kind
    (succ (succ zero))
    (@face_comp
      (succ (succ zero))
      (succ (succ zero))
      (succ (succ (succ zero)))
      simplex_edge_zero_one_code
      (@face_identity (succ (succ zero))))
  ≡ Unit_grpd;

// Every selected kind has a whole extension and inclusion into Delta[2].
assert (kind : τ Simplex2SieveKind) ⊢
  @simplex2_sieve_inclusion kind
  : τ (Hom
      (@Psh_cat SemiDeltaPlus_cat)
      (@simplex2_sieve_extension_psh kind)
      (@StandardSimplex (succ (succ (succ zero)))));
