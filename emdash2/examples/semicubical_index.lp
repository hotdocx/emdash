/* Reviewer example: the internal augmented semicube category. */

require open emdash.emdash3_2_semicubical_index;

// Objects and Homs compute to dimensions and set-classified code paths.
assert ⊢ Obj SemiCubePlus_cat ≡ Nat_grpd;

assert (p n : τ Nat_grpd) ⊢
  Hom_cat SemiCubePlus_cat p n
  ≡ Path_cat (@CubeFaceCode p n);

// The two endpoint cofaces are distinct arrows 0 -> 1.
symbol semi_cube_left_0_1
  : τ (Hom SemiCubePlus_cat zero (succ zero))
≔ @cube_face_left zero zero cube_face_nil;

symbol semi_cube_right_0_1
  : τ (Hom SemiCubePlus_cat zero (succ zero))
≔ @cube_face_right zero zero cube_face_nil;

assertnot ⊢ semi_cube_left_0_1 ≡ semi_cube_right_0_1;

// Identity and visible composition delegate to the code owners.
assert ⊢
  @id SemiCubePlus_cat (succ zero)
  ≡ @cube_face_identity (succ zero);

assert ⊢
  @comp_fapp0
    SemiCubePlus_cat zero (succ zero) (succ zero)
    (@id SemiCubePlus_cat (succ zero))
    semi_cube_left_0_1
  ≡ semi_cube_left_0_1;

assert ⊢
  @comp_fapp0
    SemiCubePlus_cat zero (succ zero) (succ zero)
    (@id SemiCubePlus_cat (succ zero))
    semi_cube_right_0_1
  ≡ semi_cube_right_0_1;

// Hom categories are locally discrete by construction.
assert (p n : τ (Obj SemiCubePlus_cat)) ⊢
  @semi_cube_plus_hom_is_discrete p n
  : τ (IsDiscreteCat (Hom_cat SemiCubePlus_cat p n));

// Intrinsic dimensions reject a point face as an endomorphism of dimension 1.
assertnot ⊢
  semi_cube_left_0_1
  : τ (Hom SemiCubePlus_cat (succ zero) (succ zero));
