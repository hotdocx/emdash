/* Reviewer example: genuine Nat-indexed intrinsic cubical levels. */

require open emdash.emdash3_2_cubical_levels;

// Zero and successor compute through Nat elimination.
assert [C : Cat] ⊢
  @CubicalLevel_cat C zero
  ≡ C;

assert [C : Cat] (n : τ Nat_grpd) ⊢
  @CubicalLevel_cat C (succ n)
  ≡ @CubicalArrow_cat (@CubicalLevel_cat C n);

// The first three positive dimensions are edges, squares, and cubes.
assert [C : Cat] ⊢
  @CubicalLevel_cat C (succ zero)
  ≡ @CubicalArrow_cat C;

assert [C : Cat] ⊢
  @CubicalLevel_cat C (succ (succ zero))
  ≡ @CubicalSquare_cat C;

assert [C : Cat] ⊢
  @CubicalLevel_cat C (succ (succ (succ zero)))
  ≡ @CubicalArrow_cat (@CubicalSquare_cat C);

// Successor is a genuine new arrow level, not the old category by alias.
assertnot [C : Cat] ⊢
  @CubicalLevel_cat C (succ zero)
  ≡ C;
