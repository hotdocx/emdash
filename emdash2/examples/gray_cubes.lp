/*
  Reviewer example: fixed-bracketing positive-dimensional Gray cubes.

  The predecessor index avoids asserting a tensor unit that the selected
  right-closure boundary does not provide.  Dimensions one through three
  compute directly from Nat recursion; alternate bracketings and coordinate
  symmetries remain explicit nonclaims.
*/

require open emdash.emdash3_2_gray_cubes;

assert ⊢ GrayCube1_R ≡ WalkingArrow_cat;

assert ⊢
  GrayCube2_R
  ≡ @GrayTensor_R WalkingArrow_cat WalkingArrow_cat;

assert ⊢
  GrayCube3_R
  ≡ @GrayTensor_R
      WalkingArrow_cat
      (@GrayTensor_R WalkingArrow_cat WalkingArrow_cat);

assert (n : τ Nat_grpd) ⊢
  @GrayCubePos_R (succ n)
  ≡ @GrayTensor_R WalkingArrow_cat (@GrayCubePos_R n);
