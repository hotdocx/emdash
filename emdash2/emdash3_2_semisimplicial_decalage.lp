/*
  Categorical decalage and a fixed semisimplicial cone fibre.

  The index shift appends one final vertex and acts on face codes by keep.
  Whole base and cone transformations retain generic naturality. Presheaf
  decalage is ordinary restriction along that shift. For a groupoid-valued
  diagram and fixed vertex x, the selected level-n cone fibre is the homotopy
  fibre of the cone-vertex observation; forgetting the tip is one whole
  Path-map functor to the opposite base simplex.

  The module stops at the checked levelwise Sigma/HFiber boundary. No active
  varying-HFiber Catd owner currently assembles these fibres into one displayed
  semisimplicial object, so the whole comparison with `homd_int` is explicitly
  deferred rather than replaced by a pointwise analogy. It adds no unifier or
  external naturality record.
*/

require open emdash.emdash3_2_semisimplicial_diagrams;

// Unique empty face into an n-vertex ordinal.
symbol face_empty
  (n : τ Nat_grpd)
  : τ (@FaceCode zero n)
≔ @nat_elim
    (λ n0 : τ Nat_grpd, @FaceCode zero n0)
    face_nil
    (λ n0 : τ Nat_grpd,
      λ previous : τ (@FaceCode zero n0),
        @face_skip zero n0 previous)
    n;

// Append one final vertex to objects and retain it in every face code.
injective symbol semi_delta_shift_func
  : τ (Functor SemiDeltaPlus_cat SemiDeltaPlus_cat);

rule @fapp0 _ _ semi_delta_shift_func $n
  ↪ succ $n;

// lhs-audit: keep 1,2 -- rigid index categories guard this selected action.
rule @fapp1_fapp0
      SemiDeltaPlus_cat SemiDeltaPlus_cat
      semi_delta_shift_func _ _ $f
  ↪ @face_keep _ _ $f;

// Old vertices form the base face; the newly appended vertex is the cone tip.
symbol semi_delta_base_face
  (n : τ Nat_grpd)
  : τ (@FaceCode n (succ n))
≔ @face_skip n n (@face_identity n);

symbol semi_delta_cone_vertex
  (n : τ Nat_grpd)
  : τ (@FaceCode (succ zero) (succ n))
≔ @face_keep zero n (@face_empty n);

// Whole natural families of base inclusions and cone-tip inclusions.
injective symbol semi_delta_base_transf
  : τ (Transf
      (@id_func SemiDeltaPlus_cat)
      semi_delta_shift_func);

rule @tapp0_fapp0 _ _ _ _ $n semi_delta_base_transf
  ↪ @semi_delta_base_face $n;

injective symbol semi_delta_cone_transf
  : τ (Transf
      (@Const_func
        SemiDeltaPlus_cat SemiDeltaPlus_cat (succ zero))
      semi_delta_shift_func);

rule @tapp0_fapp0 _ _ _ _ $n semi_delta_cone_transf
  ↪ @semi_delta_cone_vertex $n;

// Categorical decalage is ordinary presheaf restriction along the shift.
symbol semisimplicial_decalage_func
  : τ (Functor
      (@Psh_cat SemiDeltaPlus_cat)
      (@Psh_cat SemiDeltaPlus_cat))
≔ @Psh_pullback_func
    SemiDeltaPlus_cat SemiDeltaPlus_cat
    semi_delta_shift_func;

symbol semisimplicial_decalage
  (X : τ (@Psh SemiDeltaPlus_cat))
  : τ (@Psh SemiDeltaPlus_cat)
≔ @fapp0
    (@Psh_cat SemiDeltaPlus_cat)
    (@Psh_cat SemiDeltaPlus_cat)
    semisimplicial_decalage_func
    X;

// Groupoid-valued base and cone observations at dimension n.
symbol semisimplicial_cone_base_map
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (n : τ Nat_grpd)
  : τ (@Function_grpd
      (@semisimplicial_grpd_level X (succ n))
      (@semisimplicial_grpd_level X n))
≔ @semisimplicial_grpd_face_map
    X n (succ n) (@semi_delta_base_face n);

symbol semisimplicial_cone_vertex_map
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (n : τ Nat_grpd)
  : τ (@Function_grpd
      (@semisimplicial_grpd_level X (succ n))
      (@semisimplicial_grpd_level X (succ zero)))
≔ @semisimplicial_grpd_face_map
    X (succ zero) (succ n) (@semi_delta_cone_vertex n);

// Simplices whose final cone vertex is the fixed x.
symbol SemisimplicialConeFibre
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  (x : τ (@semisimplicial_grpd_level X (succ zero)))
  (n : τ Nat_grpd)
  : Grpd
≔ @HFiber
    (@semisimplicial_grpd_level X (succ n))
    (@semisimplicial_grpd_level X (succ zero))
    (@semisimplicial_cone_vertex_map X n)
    x;

// Forget the cone tip and return the opposite base simplex.
symbol semisimplicial_cone_base_function
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [x : τ (@semisimplicial_grpd_level X (succ zero))]
  (n : τ Nat_grpd)
  : τ (@Function_grpd
      (@SemisimplicialConeFibre X x n)
      (@semisimplicial_grpd_level X n))
≔ λ h : τ (@SemisimplicialConeFibre X x n),
    @semisimplicial_cone_base_map X n
      (@hfiber_point
        (@semisimplicial_grpd_level X (succ n))
        (@semisimplicial_grpd_level X (succ zero))
        (@semisimplicial_cone_vertex_map X n)
        x h);

symbol semisimplicial_cone_base_func
  [X : τ (Obj SemiSimplicialGrpd_cat)]
  [x : τ (@semisimplicial_grpd_level X (succ zero))]
  (n : τ Nat_grpd)
  : τ (Functor
      (Path_cat (@SemisimplicialConeFibre X x n))
      (Path_cat (@semisimplicial_grpd_level X n)))
≔ @path_map_func
    (@SemisimplicialConeFibre X x n)
    (@semisimplicial_grpd_level X n)
    (@semisimplicial_cone_base_function X x n);
