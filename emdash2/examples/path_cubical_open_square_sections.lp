/* Reviewer example: restrictions, sections, and whole Path action. */

require open emdash.emdash3_2_path_cubical_open_square_actions;

// Restriction of a visible square keeps exactly the selected three edges.
assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_square_restrict_missing_b A
    (@path_cube_square A x00 x01 x10 x11 u v a b alpha)
  ≡ @path_open_square_missing_b_intro A x00 x01 x10 x11 u v a;

assert [A : Grpd]
  (x00 x01 x10 x11 : τ A)
  (u : τ (@= A x00 x01))
  (v : τ (@= A x10 x11))
  (a : τ (@= A x00 x10))
  (b : τ (@= A x01 x11))
  (alpha : τ (@PathSquareFiller_grpd A x00 x01 x10 x11 u v a b)) ⊢
  @path_square_restrict_missing_u A
    (@path_cube_square A x00 x01 x10 x11 u v a b alpha)
  ≡ @path_open_square_missing_u_intro A x00 x01 x10 x11 v a b;

// All four algebraic fillers are sections of their restrictions.
assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingU_grpd A)) ⊢
  @path_open_square_missing_u_section A box
  : τ (@= (@PathOpenSquareMissingU_grpd A)
      (@path_square_restrict_missing_u
        A (@path_open_square_fill_missing_u A box))
      box);

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingV_grpd A)) ⊢
  @path_open_square_missing_v_section A box
  : τ (@= (@PathOpenSquareMissingV_grpd A)
      (@path_square_restrict_missing_v
        A (@path_open_square_fill_missing_v A box))
      box);

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingA_grpd A)) ⊢
  @path_open_square_missing_a_section A box
  : τ (@= (@PathOpenSquareMissingA_grpd A)
      (@path_square_restrict_missing_a
        A (@path_open_square_fill_missing_a A box))
      box);

assert [A : Grpd]
  (box : τ (@PathOpenSquareMissingB_grpd A)) ⊢
  @path_open_square_missing_b_section A box
  : τ (@= (@PathOpenSquareMissingB_grpd A)
      (@path_square_restrict_missing_b
        A (@path_open_square_fill_missing_b A box))
      box);

// Fillers and restrictions act as whole Path functors.
assert [A : Grpd] ⊢
  @path_open_square_fill_missing_b_func A
  : τ (Functor
      (Path_cat (@PathOpenSquareMissingB_grpd A))
      (Path_cat (@PathCube_grpd A (succ (succ zero)))));

assert [A : Grpd] ⊢
  @path_square_restrict_missing_b_func A
  : τ (Functor
      (Path_cat (@PathCube_grpd A (succ (succ zero))))
      (Path_cat (@PathOpenSquareMissingB_grpd A)));

// The whole function section path retains equality-valued transfor action.
assert [A : Grpd] ⊢
  @path_open_square_missing_b_section_transf A
  : τ (Transf
      (@path_map_func
        (@PathOpenSquareMissingB_grpd A)
        (@PathOpenSquareMissingB_grpd A)
        (λ box : τ (@PathOpenSquareMissingB_grpd A),
          @path_square_restrict_missing_b
            A (@path_open_square_fill_missing_b A box)))
      (@path_map_func
        (@PathOpenSquareMissingB_grpd A)
        (@PathOpenSquareMissingB_grpd A)
        (λ box : τ (@PathOpenSquareMissingB_grpd A), box)));

// One next hom action is explicit and iterable.
assert [A : Grpd]
  (X Y : τ (@PathOpenSquareMissingB_grpd A)) ⊢
  @path_open_square_fill_missing_b_hom_func A X Y
  : τ (Functor
      (Path_cat (@= (@PathOpenSquareMissingB_grpd A) X Y))
      (Path_cat (@=
        (@PathCube_grpd A (succ (succ zero)))
        (@path_open_square_fill_missing_b A X)
        (@path_open_square_fill_missing_b A Y))));

type @path_cube_square_ind;
type @path_square_restrict_missing_b;
type @path_open_square_missing_b_section;
type @path_open_square_fill_missing_b_func;
