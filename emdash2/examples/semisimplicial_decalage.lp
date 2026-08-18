/*
  Focused reviewer for categorical semisimplicial decalage.

  The index shift appends one vertex, while whole base and cone-tip
  transformations retain the generic transformation action.  Presheaf
  restriction therefore realizes Dec(X)[n] = X[n+1].  For a fixed cone tip,
  the first three selected fibres and their whole Path-map to the base are
  checked levelwise.  No varying-HFiber displayed family or whole homd_
  comparison is claimed.
*/

require open emdash.emdash3_2_semisimplicial_decalage;

// The index shift appends one final vertex.
assert (n : τ Nat_grpd) ⊢
  @fapp0
    SemiDeltaPlus_cat SemiDeltaPlus_cat
    semi_delta_shift_func n
  ≡ succ n;

// Its whole arrow action retains the old face and keeps the new vertex.
assert
  [p n : τ Nat_grpd]
  (f : τ (@FaceCode p n)) ⊢
  @fapp1_fapp0
    SemiDeltaPlus_cat SemiDeltaPlus_cat
    semi_delta_shift_func p n f
  ≡ @face_keep p n f;

// The low-dimensional base and cone-tip faces have the intended codes.
assert ⊢
  @semi_delta_base_face zero
  ≡ @face_skip zero zero face_nil;

assert ⊢
  @semi_delta_cone_vertex zero
  ≡ @face_keep zero zero face_nil;

// Both observations are components of whole transformations.
assert (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    SemiDeltaPlus_cat SemiDeltaPlus_cat
    (@id_func SemiDeltaPlus_cat)
    semi_delta_shift_func
    n semi_delta_base_transf
  ≡ @semi_delta_base_face n;

assert (n : τ Nat_grpd) ⊢
  @tapp0_fapp0
    SemiDeltaPlus_cat SemiDeltaPlus_cat
    (@Const_func
      SemiDeltaPlus_cat SemiDeltaPlus_cat (succ zero))
    semi_delta_shift_func
    n semi_delta_cone_transf
  ≡ @semi_delta_cone_vertex n;

// Naturality remains at the generic iterable transformation owner.
assert (p n : τ Nat_grpd) ⊢
  @tapp1_func
    SemiDeltaPlus_cat SemiDeltaPlus_cat
    (@id_func SemiDeltaPlus_cat)
    semi_delta_shift_func
    p n semi_delta_base_transf
  : τ (Functor
      (Hom_cat SemiDeltaPlus_cat p n)
      (Hom_cat SemiDeltaPlus_cat p (succ n)));

// Decalage is restriction along the shift and hence shifts every fibre.
assert
  (X : τ (@Psh SemiDeltaPlus_cat))
  (n : τ Nat_grpd) ⊢
  Fibre_cat (@semisimplicial_decalage X) n
  ≡ Fibre_cat X (succ n);

// The first three selected cone fibres are internal groupoids.
assert
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (x : τ (@semisimplicial_grpd_level X (succ zero))) ⊢
  @SemisimplicialConeFibre X x zero
  : Grpd;

assert
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (x : τ (@semisimplicial_grpd_level X (succ zero))) ⊢
  @SemisimplicialConeFibre X x (succ zero)
  : Grpd;

assert
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (x : τ (@semisimplicial_grpd_level X (succ zero))) ⊢
  @SemisimplicialConeFibre X x (succ (succ zero))
  : Grpd;

// Forgetting the cone tip is one whole Path-map, not only a point function.
assert
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [x : τ (@semisimplicial_grpd_level X (succ zero))]
  (n : τ Nat_grpd) ⊢
  @semisimplicial_cone_base_func X x n
  ≡ @path_map_func
      (@SemisimplicialConeFibre X x n)
      (@semisimplicial_grpd_level X n)
      (@semisimplicial_cone_base_function X x n);

// One next action remains at that generic Path-map owner.
assert
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [x : τ (@semisimplicial_grpd_level X (succ zero))]
  (n : τ Nat_grpd)
  (h k : τ (@SemisimplicialConeFibre X x n)) ⊢
  @fapp1_func
    (Path_cat (@SemisimplicialConeFibre X x n))
    (Path_cat (@semisimplicial_grpd_level X n))
    (@semisimplicial_cone_base_func X x n)
    h k
  : τ (Functor
      (Path_cat (@= (@SemisimplicialConeFibre X x n) h k))
      (Path_cat (@=
        (@semisimplicial_grpd_level X n)
        (@semisimplicial_cone_base_function X x n h)
        (@semisimplicial_cone_base_function X x n k))));

// A pointwise cone fibre is not silently identified with the base level.
assertnot
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [x : τ (@semisimplicial_grpd_level X (succ zero))]
  (n : τ Nat_grpd) ⊢
  @SemisimplicialConeFibre X x n
  ≡ @semisimplicial_grpd_level X n;
