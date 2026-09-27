/*
  Emdash v3.2: algebraic fillers for all four path-groupoidal open squares.

  The selected paths reuse the existing path-groupoid horn-zero/horn-two
  formulas. Their J-derived cancellation proofs are reframed from transparent
  `eq_trans` endpoints to the categorical `comp_fapp0(Path_cat(...))`
  endpoints expected by `PathSquareFiller_grpd`. Each result is then the
  existing native `path_cube_square` constructor.

  This module is transparent and rule-free. It adds no filler axiom,
  associativity/cancellation duplicate, interval, solver, or unifier.
*/

require open emdash.emdash3_2_path_cubical_open_square_frames;
require open emdash.emdash3_2_path_groupoid_2horn_fillers;

// Reframe an eq_trans square equality to the active categorical Path endpoints.
symbol path_square_filler_from_eq_trans
  [A : Grpd]
  [x00 x01 x10 x11 : τ A]
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (q : τ (@=
    (@= A x00 x11)
    (@eq_trans A x00 x01 x11 u b)
    (@eq_trans A x00 x10 x11 a v)))
  : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)
≔ @eq_trans
    (@= A x00 x11)
    (@comp_fapp0 (Path_cat A) x00 x01 x11 b u)
    (@eq_trans A x00 x01 x11 u b)
    (@comp_fapp0 (Path_cat A) x00 x10 x11 v a)
    (@path_comp_eq_trans A x00 x01 u x11 b)
    (@eq_trans
      (@= A x00 x11)
      (@eq_trans A x00 x01 x11 u b)
      (@eq_trans A x00 x10 x11 a v)
      (@comp_fapp0 (Path_cat A) x00 x10 x11 v a)
      q
      (@eq_sym
        (@= A x00 x11)
        (@comp_fapp0 (Path_cat A) x00 x10 x11 v a)
        (@eq_trans A x00 x10 x11 a v)
        (@path_comp_eq_trans A x00 x10 a x11 v)));

// Missing b: first compose v o a, then solve the outer horn against u.
symbol path_open_square_missing_b_p02
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@= A
      (path_open_square_x00 box)
      (path_open_square_x11 box))
≔ @eq_trans
    A
    (path_open_square_x00 box)
    (path_open_square_x10 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_b_a A box)
    (@path_open_square_missing_b_v A box);

symbol path_open_square_missing_b_edge
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@= A
      (path_open_square_x01 box)
      (path_open_square_x11 box))
≔ @eq_trans
    A
    (path_open_square_x01 box)
    (path_open_square_x00 box)
    (path_open_square_x11 box)
    (@eq_sym
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (@path_open_square_missing_b_u A box))
    (@path_open_square_missing_b_p02 A box);

symbol path_open_square_missing_b_alpha_raw
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@=
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x01 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_b_u A box)
        (@path_open_square_missing_b_edge A box))
      (@path_open_square_missing_b_p02 A box))
≔ @path_nerve2_horn_zero_cancel
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (@path_open_square_missing_b_u A box)
    (path_open_square_x11 box)
    (@path_open_square_missing_b_p02 A box);

symbol path_open_square_fill_missing_b
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_cube_square
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (path_open_square_x10 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_b_u A box)
    (@path_open_square_missing_b_v A box)
    (@path_open_square_missing_b_a A box)
    (@path_open_square_missing_b_edge A box)
    (@path_square_filler_from_eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_b_u A box)
      (@path_open_square_missing_b_v A box)
      (@path_open_square_missing_b_a A box)
      (@path_open_square_missing_b_edge A box)
      (@path_open_square_missing_b_alpha_raw A box));

// Missing v: solve the outer horn against a, then reverse its cancellation.
symbol path_open_square_missing_v_p02
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@= A
      (path_open_square_x00 box)
      (path_open_square_x11 box))
≔ @eq_trans
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_v_u A box)
    (@path_open_square_missing_v_b A box);

symbol path_open_square_missing_v_edge
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@= A
      (path_open_square_x10 box)
      (path_open_square_x11 box))
≔ @eq_trans
    A
    (path_open_square_x10 box)
    (path_open_square_x00 box)
    (path_open_square_x11 box)
    (@eq_sym
      A
      (path_open_square_x00 box)
      (path_open_square_x10 box)
      (@path_open_square_missing_v_a A box))
    (@path_open_square_missing_v_p02 A box);

symbol path_open_square_missing_v_alpha_raw
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@=
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@path_open_square_missing_v_p02 A box)
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x10 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_v_a A box)
        (@path_open_square_missing_v_edge A box)))
≔ @eq_sym
    (@= A (path_open_square_x00 box) (path_open_square_x11 box))
    (@eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_v_a A box)
      (@path_open_square_missing_v_edge A box))
    (@path_open_square_missing_v_p02 A box)
    (@path_nerve2_horn_zero_cancel
      A
      (path_open_square_x00 box)
      (path_open_square_x10 box)
      (@path_open_square_missing_v_a A box)
      (path_open_square_x11 box)
      (@path_open_square_missing_v_p02 A box));

symbol path_open_square_fill_missing_v
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_cube_square
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (path_open_square_x10 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_v_u A box)
    (@path_open_square_missing_v_edge A box)
    (@path_open_square_missing_v_a A box)
    (@path_open_square_missing_v_b A box)
    (@path_square_filler_from_eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_v_u A box)
      (@path_open_square_missing_v_edge A box)
      (@path_open_square_missing_v_a A box)
      (@path_open_square_missing_v_b A box)
      (@path_open_square_missing_v_alpha_raw A box));

// Missing u: solve the right-oriented horn against b.
symbol path_open_square_missing_u_p02
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@= A
      (path_open_square_x00 box)
      (path_open_square_x11 box))
≔ @eq_trans
    A
    (path_open_square_x00 box)
    (path_open_square_x10 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_u_a A box)
    (@path_open_square_missing_u_v A box);

symbol path_open_square_missing_u_edge
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@= A
      (path_open_square_x00 box)
      (path_open_square_x01 box))
≔ @eq_trans_right
    A
    (path_open_square_x00 box)
    (path_open_square_x11 box)
    (path_open_square_x01 box)
    (@path_open_square_missing_u_p02 A box)
    (@eq_sym
      A
      (path_open_square_x01 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_u_b A box));

symbol path_open_square_missing_u_alpha_raw
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@=
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x01 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_u_edge A box)
        (@path_open_square_missing_u_b A box))
      (@path_open_square_missing_u_p02 A box))
≔ @eq_trans
    (@= A (path_open_square_x00 box) (path_open_square_x11 box))
    (@eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_u_edge A box)
      (@path_open_square_missing_u_b A box))
    (@eq_trans_right
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_u_edge A box)
      (@path_open_square_missing_u_b A box))
    (@path_open_square_missing_u_p02 A box)
    (@eq_sym
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@eq_trans_right
        A
        (path_open_square_x00 box)
        (path_open_square_x01 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_u_edge A box)
        (@path_open_square_missing_u_b A box))
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x01 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_u_edge A box)
        (@path_open_square_missing_u_b A box))
      (@eq_trans_right_agrees
        A
        (path_open_square_x00 box)
        (path_open_square_x01 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_u_edge A box)
        (@path_open_square_missing_u_b A box)))
    (@path_nerve2_horn_two_cancel
      A
      (path_open_square_x01 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_u_b A box)
      (path_open_square_x00 box)
      (@path_open_square_missing_u_p02 A box));

symbol path_open_square_fill_missing_u
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_cube_square
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (path_open_square_x10 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_u_edge A box)
    (@path_open_square_missing_u_v A box)
    (@path_open_square_missing_u_a A box)
    (@path_open_square_missing_u_b A box)
    (@path_square_filler_from_eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_u_edge A box)
      (@path_open_square_missing_u_v A box)
      (@path_open_square_missing_u_a A box)
      (@path_open_square_missing_u_b A box)
      (@path_open_square_missing_u_alpha_raw A box));

// Missing a: solve the right-oriented horn against v, then reverse it.
symbol path_open_square_missing_a_p02
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@= A
      (path_open_square_x00 box)
      (path_open_square_x11 box))
≔ @eq_trans
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_a_u A box)
    (@path_open_square_missing_a_b A box);

symbol path_open_square_missing_a_edge
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@= A
      (path_open_square_x00 box)
      (path_open_square_x10 box))
≔ @eq_trans_right
    A
    (path_open_square_x00 box)
    (path_open_square_x11 box)
    (path_open_square_x10 box)
    (@path_open_square_missing_a_p02 A box)
    (@eq_sym
      A
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_a_v A box));

symbol path_open_square_missing_a_target_raw
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@=
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x10 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_a_edge A box)
        (@path_open_square_missing_a_v A box))
      (@path_open_square_missing_a_p02 A box))
≔ @eq_trans
    (@= A (path_open_square_x00 box) (path_open_square_x11 box))
    (@eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_a_edge A box)
      (@path_open_square_missing_a_v A box))
    (@eq_trans_right
      A
      (path_open_square_x00 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_a_edge A box)
      (@path_open_square_missing_a_v A box))
    (@path_open_square_missing_a_p02 A box)
    (@eq_sym
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@eq_trans_right
        A
        (path_open_square_x00 box)
        (path_open_square_x10 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_a_edge A box)
        (@path_open_square_missing_a_v A box))
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x10 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_a_edge A box)
        (@path_open_square_missing_a_v A box))
      (@eq_trans_right_agrees
        A
        (path_open_square_x00 box)
        (path_open_square_x10 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_a_edge A box)
        (@path_open_square_missing_a_v A box)))
    (@path_nerve2_horn_two_cancel
      A
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_a_v A box)
      (path_open_square_x00 box)
      (@path_open_square_missing_a_p02 A box));

symbol path_open_square_missing_a_alpha_raw
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@=
      (@= A (path_open_square_x00 box) (path_open_square_x11 box))
      (@path_open_square_missing_a_p02 A box)
      (@eq_trans
        A
        (path_open_square_x00 box)
        (path_open_square_x10 box)
        (path_open_square_x11 box)
        (@path_open_square_missing_a_edge A box)
        (@path_open_square_missing_a_v A box)))
≔ @eq_sym
    (@= A (path_open_square_x00 box) (path_open_square_x11 box))
    (@eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_a_edge A box)
      (@path_open_square_missing_a_v A box))
    (@path_open_square_missing_a_p02 A box)
    (@path_open_square_missing_a_target_raw A box);

symbol path_open_square_fill_missing_a
  [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A))
  : τ (@PathCube_grpd A (succ (succ zero)))
≔ @path_cube_square
    A
    (path_open_square_x00 box)
    (path_open_square_x01 box)
    (path_open_square_x10 box)
    (path_open_square_x11 box)
    (@path_open_square_missing_a_u A box)
    (@path_open_square_missing_a_v A box)
    (@path_open_square_missing_a_edge A box)
    (@path_open_square_missing_a_b A box)
    (@path_square_filler_from_eq_trans
      A
      (path_open_square_x00 box)
      (path_open_square_x01 box)
      (path_open_square_x10 box)
      (path_open_square_x11 box)
      (@path_open_square_missing_a_u A box)
      (@path_open_square_missing_a_v A box)
      (@path_open_square_missing_a_edge A box)
      (@path_open_square_missing_a_b A box)
      (@path_open_square_missing_a_alpha_raw A box));
