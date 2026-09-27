/*
  Emdash v3.2: bounded two-dimensional path `hcomp`/`hfill` facade.

  For each selected three-edge box, `path_hcomp2_missing_*` is the missing
  path chosen by the existing horn algebra and `path_hfill2_missing_*` is the
  completed native square. The existing restriction-section proofs are the
  boundary computation laws.

  This is terminology for the completed fixed-dimensional construction, not a
  primitive Kan operation or arbitrary cofibration interface.
*/

require open emdash.emdash3_2_path_cubical_open_square_actions;
require open emdash.emdash3_2_path_cubical_open_square_sieve_realization;

symbol path_hcomp2_missing_u [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@= A (path_open_square_x00 box) (path_open_square_x01 box))
≔ @path_open_square_missing_u_edge A box;

symbol path_hcomp2_missing_v [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@= A (path_open_square_x10 box) (path_open_square_x11 box))
≔ @path_open_square_missing_v_edge A box;

symbol path_hcomp2_missing_a [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@= A (path_open_square_x00 box) (path_open_square_x10 box))
≔ @path_open_square_missing_a_edge A box;

symbol path_hcomp2_missing_b [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@= A (path_open_square_x01 box) (path_open_square_x11 box))
≔ @path_open_square_missing_b_edge A box;

symbol path_hfill2_missing_u [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_open_square_fill_missing_u A box;

symbol path_hfill2_missing_v [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_open_square_fill_missing_v A box;

symbol path_hfill2_missing_a [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_open_square_fill_missing_a A box;

symbol path_hfill2_missing_b [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_open_square_fill_missing_b A box;

// Representative boundary beta, inherited from the algebraic section.
symbol path_hfill2_missing_b_beta [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@=
      (@PathOpenSquareMissingB_grpd A)
      (@path_square_restrict_missing_b A (@path_hfill2_missing_b A box))
      box)
≔ @path_open_square_missing_b_section A box;
