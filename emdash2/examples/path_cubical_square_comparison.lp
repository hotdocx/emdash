/* Reviewer example: native path squares and equality of path edges. */

require open emdash.emdash3_2_path_cubical_square_comparison;

// The selected filler is the directed square equality b o u = v o a.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_square_edge_path A x00 x01 x10 x11 u v a b alpha
  : τ (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v);

// Reading the visible native square uses its existing nested Sigma fields.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_native_square_edge_path
    A x00 x01 x10 x11 u v
    (@cubical_square
      (Path_cat A)
      x00 x10 x01 x11
      u v a b alpha)
  ≡ @path_square_edge_path
      A x00 x01 x10 x11 u v a b alpha;

// The readback is whole on the path core of the native square Hom.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11)) ⊢
  @path_native_square_core_readback_func
    A x00 x01 x10 x11 u v
  : τ (Functor
      (Path_cat (Obj (@PathNativeSquareHom_cat
        A x00 x01 x10 x11 u v)))
      (Path_cat (@PathEdgeEquality_grpd
        A x00 x01 x10 x11 u v)));

// Its point computation is the J-derived square readback.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @fapp0
    (Path_cat (Obj (@PathNativeSquareHom_cat
      A x00 x01 x10 x11 u v)))
    (Path_cat (@PathEdgeEquality_grpd
      A x00 x01 x10 x11 u v))
    (@path_native_square_core_readback_func
      A x00 x01 x10 x11 u v)
    (@cubical_square
      (Path_cat A)
      x00 x10 x01 x11
      u v a b alpha)
  ≡ @path_square_edge_path
      A x00 x01 x10 x11 u v a b alpha;

// The reverse comparison is exactly the existing whole core inclusion.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11)) ⊢
  @path_edge_path_to_native_square_func
    A x00 x01 x10 x11 u v
  ≡ @core_incl_hom_func
      (@PathCubicalLevel_cat A (succ zero))
      (@path_cube_edge A x00 x01 u)
      (@path_cube_edge A x10 x11 v);

// The first higher equality action remains an ordinary whole functor.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (S T : τ (Obj (@PathNativeSquareHom_cat
    A x00 x01 x10 x11 u v))) ⊢
  @path_native_square_core_readback_hom_func
    A x00 x01 x10 x11 u v S T
  : τ (Functor
      (Path_cat (@=
        (Obj (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v))
        S T))
      (Path_cat (@=
        (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v)
        (@path_native_square_edge_path
          A x00 x01 x10 x11 u v S)
        (@path_native_square_edge_path
          A x00 x01 x10 x11 u v T))));

// An arbitrary directed category does not acquire this path readback.
assertnot [C : Cat]
  [x00 x01 x10 x11 : τ (Obj C)]
  (u : τ (Hom C x00 x01))
  (v : τ (Hom C x10 x11))
  (a : τ (Hom C x00 x10))
  (b : τ (Hom C x01 x11))
  (alpha : τ (Obj (@homdc_square_fibre C x00 x10 x01 x11 u v a b))) ⊢
  @lax_square C x00 x10 x01 x11 u v a b alpha
  : τ (@= (Obj (@LaxArrow_cat C))
      (@lax_edge C x00 x01 u)
      (@lax_edge C x10 x11 v));

type @path_square_edge_path;
type @path_native_square_core_readback_func;
type @path_edge_path_to_native_square_func;
