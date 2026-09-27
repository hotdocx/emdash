/* Reviewer example: the four algebraic path-groupoidal open-square fillers. */

require open emdash.emdash3_2_path_cubical_open_square_fillers;

// All four explicit three-edge carriers are independently constructible.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_u_intro A x00 x01 x10 x11 v a b
  : τ (@PathOpenSquareMissingU_grpd A);

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_v_intro A x00 x01 x10 x11 u a b
  : τ (@PathOpenSquareMissingV_grpd A);

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_a_intro A x00 x01 x10 x11 u v b
  : τ (@PathOpenSquareMissingA_grpd A);

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10)) ⊢
  @path_open_square_missing_b_intro A x00 x01 x10 x11 u v a
  : τ (@PathOpenSquareMissingB_grpd A);

// Constructor projections retain the three supplied edges.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10)) ⊢
  @path_open_square_missing_b_u A
    (@path_open_square_missing_b_intro A x00 x01 x10 x11 u v a)
  ≡ u;

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_u_b A
    (@path_open_square_missing_u_intro A x00 x01 x10 x11 v a b)
  ≡ b;

// The selected missing paths are the expected groupoidal composites.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10)) ⊢
  @path_open_square_missing_b_edge A
    (@path_open_square_missing_b_intro A x00 x01 x10 x11 u v a)
  ≡ @eq_trans
      A x01 x00 x11
      (@eq_sym A x00 x01 u)
      (@eq_trans A x00 x10 x11 a v);

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_v_edge A
    (@path_open_square_missing_v_intro A x00 x01 x10 x11 u a b)
  ≡ @eq_trans
      A x10 x00 x11
      (@eq_sym A x00 x10 a)
      (@eq_trans A x00 x01 x11 u b);

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_u_edge A
    (@path_open_square_missing_u_intro A x00 x01 x10 x11 v a b)
  ≡ @eq_trans_right
      A x00 x11 x01
      (@eq_trans A x00 x10 x11 a v)
      (@eq_sym A x01 x11 b);

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (b : τ (@= A x01 x11)) ⊢
  @path_open_square_missing_a_edge A
    (@path_open_square_missing_a_intro A x00 x01 x10 x11 u v b)
  ≡ @eq_trans_right
      A x00 x11 x10
      (@eq_trans A x00 x01 x11 u b)
      (@eq_sym A x10 x11 v);

// Every selected filler is an existing native dimension-two path cube.
assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) ⊢
  @path_open_square_fill_missing_u A box
  : τ (@PathCube_grpd A (succ (succ zero)));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A)) ⊢
  @path_open_square_fill_missing_v A box
  : τ (@PathCube_grpd A (succ (succ zero)));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) ⊢
  @path_open_square_fill_missing_a A box
  : τ (@PathCube_grpd A (succ (succ zero)));

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) ⊢
  @path_open_square_fill_missing_b A box
  : τ (@PathCube_grpd A (succ (succ zero)));

type @PathOpenSquareFrame_grpd;
type @path_open_square_frame_ind;
type @path_open_square_fill_missing_u;
type @path_open_square_fill_missing_v;
type @path_open_square_fill_missing_a;
type @path_open_square_fill_missing_b;
