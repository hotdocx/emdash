/* Reviewer example: one eliminator for every path-cubical successor. */

require open emdash.emdash3_2_path_cubical_successor_elim;

// Constructor elimination computes at arbitrary dimension.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (X Y : τ (@PathCube_grpd A n))
  (theta : τ (Hom (@PathCubicalLevel_cat A n) X Y))
  (Q : τ (@PathCube_grpd A (succ n)) → Grpd)
  (c : Π X0 : τ (@PathCube_grpd A n),
       Π Y0 : τ (@PathCube_grpd A n),
       Π theta0 : τ (Hom (@PathCubicalLevel_cat A n) X0 Y0),
       τ (Q (@path_cube_succ A n X0 Y0 theta0))) ⊢
  @path_cube_succ_ind
    A n Q c (@path_cube_succ A n X Y theta)
  ≡ c X Y theta;

// All three projections compute on the visible constructor.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (X Y : τ (@PathCube_grpd A n))
  (theta : τ (Hom (@PathCubicalLevel_cat A n) X Y)) ⊢
  @path_cube_succ_src A n (@path_cube_succ A n X Y theta)
  ≡ X;

assert [A : Grpd]
  (n : τ Nat_grpd)
  (X Y : τ (@PathCube_grpd A n))
  (theta : τ (Hom (@PathCubicalLevel_cat A n) X Y)) ⊢
  @path_cube_succ_tgt A n (@path_cube_succ A n X Y theta)
  ≡ Y;

assert [A : Grpd]
  (n : τ Nat_grpd)
  (X Y : τ (@PathCube_grpd A n))
  (theta : τ (Hom (@PathCubicalLevel_cat A n) X Y)) ⊢
  @path_cube_succ_cell A n (@path_cube_succ A n X Y theta)
  ≡ theta;

// Constructor eta is reflexive for a visible successor and remains
// propositionally available for an arbitrary cube.
assert [A : Grpd]
  (n : τ Nat_grpd)
  (X Y : τ (@PathCube_grpd A n))
  (theta : τ (Hom (@PathCubicalLevel_cat A n) X Y)) ⊢
  @path_cube_succ_eta A n (@path_cube_succ A n X Y theta)
  ≡ @eq_refl
      (@PathCube_grpd A (succ n))
      (@path_cube_succ A n X Y theta);

assert [A : Grpd]
  (n : τ Nat_grpd)
  (Z : τ (@PathCube_grpd A (succ n))) ⊢
  @path_cube_succ_eta A n Z
  : τ (@=
      (@PathCube_grpd A (succ n))
      (@path_cube_succ
        A n
        (@path_cube_succ_src A n Z)
        (@path_cube_succ_tgt A n Z)
        (@path_cube_succ_cell A n Z))
      Z);

type @path_cube_succ_ind;
type @path_cube_succ_eta;
