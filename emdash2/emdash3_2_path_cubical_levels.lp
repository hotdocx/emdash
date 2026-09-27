/*
  Emdash v3.2: path-specialized intrinsic cubical levels.

  The directed cubical tower is specialized to the literal path category:

    PathCubicalLevel_cat(A,n) = CubicalLevel_cat(Path_cat(A),n),
    PathCube_grpd(A,n)        = Obj(PathCubicalLevel_cat(A,n)).

  Level zero is A. A successor object is an arrow of the preceding level, so
  paths, squares, cubes, and all later cells reuse the existing
  homdc_int/Sigma/LaxArrow recursion. In dimension two the generic directed
  square filler becomes the equality

    b o u = v o a.

  This module is transparent and rule-free. It introduces no interval,
  square, cube, equality, groupoidality, face, rewrite, or unifier.
*/

require open emdash.emdash3_2_cubical_levels;

// Native cubical category at dimension n for the literal path category of A.
symbol PathCubicalLevel_cat
  (A : Grpd)
  (n : τ Nat_grpd)
  : Cat
≔ @CubicalLevel_cat (Path_cat A) n;

// Groupoid of native path-cubical objects at dimension n.
symbol PathCube_grpd
  (A : Grpd)
  (n : τ Nat_grpd)
  : Grpd
≔ Obj (@PathCubicalLevel_cat A n);

// A successor cube is one arrow of the preceding cubical category.
symbol path_cube_succ
  [A : Grpd]
  [n : τ Nat_grpd]
  (X Y : τ (@PathCube_grpd A n))
  (theta : τ (Hom (@PathCubicalLevel_cat A n) X Y))
  : τ (@PathCube_grpd A (succ n))
≔ @cubical_edge
    (@PathCubicalLevel_cat A n)
    X Y theta;

// Dimension one: an equality path as a native cubical edge.
symbol path_cube_edge
  [A : Grpd]
  (x y : τ A)
  (u : τ (@= A x y))
  : τ (@PathCube_grpd A (succ zero))
≔ @path_cube_succ A zero x y u;

// Readable groupoid of fillers for the selected path-square orientation.
symbol PathSquareFiller_grpd
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  : Grpd
≔ @=
    (@= A x00 x11)
    (@comp_fapp0 (Path_cat A) x00 x01 x11 b u)
    (@comp_fapp0 (Path_cat A) x00 x10 x11 v a);

// Dimension two: the existing directed square with an equality-valued filler.
symbol path_cube_square
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_cube_succ
    A (succ zero)
    (@path_cube_edge A x00 x01 u)
    (@path_cube_edge A x10 x11 v)
    (@cubical_square
      (Path_cat A)
      x00 x10 x01 x11
      u v a b alpha);

// The two new-coordinate faces at every successor dimension.
symbol path_cube_src_func
  (A : Grpd)
  (n : τ Nat_grpd)
  : τ (Functor
      (@PathCubicalLevel_cat A (succ n))
      (@PathCubicalLevel_cat A n))
≔ @cubical_src_func (@PathCubicalLevel_cat A n);

symbol path_cube_tgt_func
  (A : Grpd)
  (n : τ Nat_grpd)
  : τ (Functor
      (@PathCubicalLevel_cat A (succ n))
      (@PathCubicalLevel_cat A n))
≔ @cubical_tgt_func (@PathCubicalLevel_cat A n);
