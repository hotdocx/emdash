/* Reviewer example: bounded path-groupoidal hcomp/hfill in dimension two. */

require open emdash.emdash3_2_path_cubical_hcomp2;

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) ⊢
  @path_hcomp2_missing_u A box
  : τ (@= A (path_open_square_x00 box) (path_open_square_x01 box));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A)) ⊢
  @path_hcomp2_missing_v A box
  : τ (@= A (path_open_square_x10 box) (path_open_square_x11 box));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) ⊢
  @path_hfill2_missing_a A box
  : τ (@PathCube_grpd A (succ (succ zero)));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) ⊢
  @path_hfill2_missing_b_beta A box
  : τ (@= (@PathOpenSquareMissingB_grpd A)
      (@path_square_restrict_missing_b A (@path_hfill2_missing_b A box))
      box);

// This API is intentionally fixed at dimension two and path-groupoidal data.
assertnot [C : Cat]
  (u : τ (Obj (@CubicalLevel_cat C (succ zero)))) ⊢
  @path_hcomp2_missing_u C u
  : τ (Obj C);

type @path_hcomp2_missing_b;
type @path_hfill2_missing_b;
