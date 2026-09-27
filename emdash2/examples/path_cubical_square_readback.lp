/* Reviewer example: generic pointwise readback of native path squares. */

require open emdash.emdash3_2_path_cubical_square_readback;

// Arbitrary native square objects determine equality of arbitrary path edges.
assert [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero)))
  (theta : τ (Obj (@Hom_cat
    (@PathCubicalLevel_cat A (succ zero)) X Y))) ⊢
  @path_native_square_path A X Y theta
  : τ (@= (@PathCube_grpd A (succ zero)) X Y);

// The generic readback computes to the visible J-derived formula.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_native_square_path
    A
    (@path_cube_edge A x00 x01 u)
    (@path_cube_edge A x10 x11 v)
    (@cubical_square
      (Path_cat A)
      x00 x10 x01 x11
      u v a b alpha)
  ≡ @path_square_edge_path
      A x00 x01 x10 x11 u v a b alpha;

// Readback has a whole equality action on the path core of the native Hom.
assert [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero))) ⊢
  @path_native_square_readback_core_func A X Y
  : τ (Functor
      (Path_cat (Obj (@Hom_cat
        (@PathCubicalLevel_cat A (succ zero)) X Y)))
      (Path_cat (@= (@PathCube_grpd A (succ zero)) X Y)));

// The reverse whole map is exactly generic core inclusion.
assert [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero))) ⊢
  @path_edge_equality_to_native_square_func A X Y
  ≡ @core_incl_hom_func
      (@PathCubicalLevel_cat A (succ zero)) X Y;

// Re-inclusion is not yet the visible-square normal form. Its propositional
// comparison and coherent cube action are exactly the closure prerequisite.
assertnot [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @fapp0
    (Path_cat (@PathEdgeEquality_grpd A x00 x01 x10 x11 u v))
    (@PathNativeSquareHom_cat A x00 x01 x10 x11 u v)
    (@path_edge_equality_to_native_square_func
      A
      (@path_cube_edge A x00 x01 u)
      (@path_cube_edge A x10 x11 v))
    (@path_square_edge_path
      A x00 x01 x10 x11 u v a b alpha)
  ≡ @cubical_square
      (Path_cat A)
      x00 x10 x01 x11
      u v a b alpha;

// One higher equality action remains available without a capped custom rule.
assert [A : Grpd]
  [X Y : τ (@PathCube_grpd A (succ zero))]
  (S T : τ (Obj (@Hom_cat
    (@PathCubicalLevel_cat A (succ zero)) X Y))) ⊢
  @path_native_square_readback_core_hom_func A X Y S T
  : τ (Functor
      (Path_cat (@=
        (Obj (@Hom_cat (@PathCubicalLevel_cat A (succ zero)) X Y))
        S T))
      (Path_cat (@=
        (@= (@PathCube_grpd A (succ zero)) X Y)
        (@path_native_square_path A X Y S)
        (@path_native_square_path A X Y T))));

// No native-Hom-to-Path functor or groupoidality evidence is assumed here.
assertnot [A : Grpd]
  (X Y : τ (@PathCube_grpd A (succ zero))) ⊢
  @path_native_square_readback_core_func A X Y
  : τ (Functor
      (@Hom_cat (@PathCubicalLevel_cat A (succ zero)) X Y)
      (Path_cat (@= (@PathCube_grpd A (succ zero)) X Y)));

type @path_native_square_path;
type @path_native_square_readback_core_func;
type @path_edge_equality_to_native_square_func;
