/*
  Reviewer milestone: adjunction cut-elimination.

  The first-class v3.2 adjunction package exposes left/right adjoint functors,
  unit/counit transfors, and component-level triangle cut-elimination.
*/

require open emdash.emdash3_2;

assert [R L : Cat]
  (J : τ (Adjunction R L))
  (X X' : τ (Obj R))
  (Y : τ (Obj L))
  (g : τ (Hom R X X'))
  (f : τ (Hom L (@fapp0 R L (@left_adj_func R L J) X') Y)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      L
      L
      (@comp_cat_fapp0
        L
        R
        L
        (@left_adj_func R L J)
        (@right_adj_func R L J))
      (@id_func L)
      (@fapp0 R L (@left_adj_func R L J) X')
      Y
      (@counit_adj_transf R L J)
      f)
    (@fapp1_fapp0
      R
      L
      (@left_adj_func R L J)
      X
      (@fapp0 L R (@right_adj_func R L J)
        (@fapp0 R L (@left_adj_func R L J) X'))
      (@tapp1_fapp0
        R
        R
        (@id_func R)
        (@comp_cat_fapp0
          R
          L
          R
          (@right_adj_func R L J)
          (@left_adj_func R L J))
        X
        X'
        (@unit_adj_transf R L J)
        g))
  ≡ comp_fapp0
      f
      (@fapp1_fapp0 R L (@left_adj_func R L J) X X' g);
