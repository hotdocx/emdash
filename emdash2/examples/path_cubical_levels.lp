/* Reviewer example: path-specialized intrinsic cubical levels. */

require open emdash.emdash3_2_path_cubical_levels;

// The facade is the existing variable-dimensional cubical tower at Path(A).
assert [A : Grpd] ⊢
  @PathCubicalLevel_cat A zero
  ≡ Path_cat A;

assert [A : Grpd] (n : τ Nat_grpd) ⊢
  @PathCubicalLevel_cat A (succ n)
  ≡ @LaxArrow_cat (@PathCubicalLevel_cat A n);

assert [A : Grpd] ⊢
  @PathCube_grpd A zero
  ≡ A;

// Dimensions one, two, and three are paths, squares, and cubes.
assert [A : Grpd] ⊢
  @PathCubicalLevel_cat A (succ zero)
  ≡ @LaxArrow_cat (Path_cat A);

assert [A : Grpd] ⊢
  @PathCubicalLevel_cat A (succ (succ zero))
  ≡ @CubicalSquare_cat (Path_cat A);

assert [A : Grpd] ⊢
  @PathCubicalLevel_cat A (succ (succ (succ zero)))
  ≡ @CubicalArrow_cat (@CubicalSquare_cat (Path_cat A));

// A path is a visible dimension-one native cube.
assert [A : Grpd]
  (x y : τ A)
  (u : τ (@= A x y)) ⊢
  @path_cube_edge A x y u
  : τ (@PathCube_grpd A (succ zero));

// Typed reflexivity confirms that the existing homdc_ filler is literally
// the equality b o u = v o a in the Path specialization.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11)) ⊢
  @eq_refl
    Grpd_grpd
    (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)
  : τ (@=
      Grpd_grpd
      (Obj (@homdc_square_fibre
        (Path_cat A)
        x00 x10 x01 x11
        u v a b))
      (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b));

// The readable square is the existing native cubical object, not a new cell.
assert [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_cube_square A x00 x01 x10 x11 u v a b alpha
  : τ (@PathCube_grpd A (succ (succ zero)));

// Both immediate successor faces remain whole functors.
assert [A : Grpd] (n : τ Nat_grpd) ⊢
  @path_cube_src_func A n
  : τ (Functor
      (@PathCubicalLevel_cat A (succ n))
      (@PathCubicalLevel_cat A n));

assert [A : Grpd] (n : τ Nat_grpd) ⊢
  @path_cube_tgt_func A n
  : τ (Functor
      (@PathCubicalLevel_cat A (succ n))
      (@PathCubicalLevel_cat A n));

// The successor does not collapse back to the preceding level.
assertnot [A : Grpd] ⊢
  @PathCubicalLevel_cat A (succ zero)
  ≡ Path_cat A;

type @PathCubicalLevel_cat;
type @PathCube_grpd;
type @path_cube_succ;
type @path_cube_square;
