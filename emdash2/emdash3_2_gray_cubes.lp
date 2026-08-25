/*
  Emdash v3.2: fixed-bracketing positive-dimensional right-Gray cubes.

  The selected right tensor has no unit comparison, so the recursion is
  indexed by the predecessor of the geometric dimension:

    GrayCubePos_R(0)       = WalkingArrow,
    GrayCubePos_R(succ n)  = WalkingArrow tensor_R GrayCubePos_R(n).

  Thus the first three values are I, I tensor_R I, and
  I tensor_R (I tensor_R I).  This is genuine Nat recursion with one fixed
  bracketing.  It adds no tensor action in parameters, zero-dimensional unit,
  associator, coordinate permutation, or Crans--Gray monoidal claim.
*/

require open emdash.emdash3_2_gray_transformation_graph;

// The (n+1)-dimensional fixed-bracketing right-Gray cube.
symbol GrayCubePos_R
  (n : τ Nat_grpd)
  : Cat
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Cat_cat)
    WalkingArrow_cat
    (λ _ : τ Nat_grpd,
      λ previous : τ (Obj Cat_cat),
        @GrayTensor_R WalkingArrow_cat previous)
    n;

// Readable selected dimensions.
symbol GrayCube1_R : Cat ≔ @GrayCubePos_R zero;

symbol GrayCube2_R : Cat ≔ @GrayCubePos_R (succ zero);

symbol GrayCube3_R : Cat ≔ @GrayCubePos_R (succ (succ zero));
