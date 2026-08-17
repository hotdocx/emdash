/*
  Focused reviewer for Path-realized pseudo-laxity.

  The generic normal-lax compositor of path_map_func is an equality between
  paths.  Equality symmetry supplies its inverse, its conventional
  eq_ap/eq_trans endpoints are propositionally related to the formal
  represented-action endpoints, and the whole transformation retains one
  iterable next-hom action.
*/

require open emdash.emdash3_2_path_pseudo_laxity;

// The whole surface is the existing generic post/left laxity transformation.
assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  (x : τ A)
  [y z : τ A]
  (q : τ (@= A y z)) ⊢
  @path_map_compositor_transf A B h x y z q
  : τ (Transf
      (@path_map_compositor_lhs_func A B h x y z q)
      (@path_map_compositor_rhs_func A B h x y z q));

// Capping the whole transformation recovers the generic compositor cell.
assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @tapp0_fapp0
    (@Hom_cat (Path_cat A) x y)
    (@Hom_cat (Path_cat B) (h x) (h z))
    (@path_map_compositor_lhs_func A B h x y z q)
    (@path_map_compositor_rhs_func A B h x y z q)
    p
    (@path_map_compositor_transf A B h x y z q)
  ≡ @path_map_compositor_path A B h x y z q p;

// The realized directed cell is a path between paths, and symmetry supplies
// its reverse without a separate pseudofunctor or inverse record.
assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_path A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p)
      (@path_map_compositor_rhs A B h x y z q p));

assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_inverse A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_rhs A B h x y z q p)
      (@path_map_compositor_lhs A B h x y z q p));

// The formal endpoints retain represented postcomposition as their runtime
// form.  Their conventional HoTT readings are supplied propositionally.
assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_lhs_agrees_readable A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p)
      (@eq_trans
        B (h x) (h y) (h z)
        (@eq_ap A B h x y p)
        (@eq_ap A B h y z q)));

assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_rhs_agrees_readable A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_rhs A B h x y z q p)
      (@eq_ap A B h x z (@eq_trans A x y z p q)));

assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_readable A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@eq_trans
        B (h x) (h y) (h z)
        (@eq_ap A B h x y p)
        (@eq_ap A B h y z q))
      (@eq_ap A B h x z (@eq_trans A x y z p q)));

assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_readable_inverse A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@eq_ap A B h x z (@eq_trans A x y z p q))
      (@eq_trans
        B (h x) (h y) (h z)
        (@eq_ap A B h x y p)
        (@eq_ap A B h y z q)));

assertnot [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_lhs A B h x y z q p
  ≡ @path_map_compositor_source_readable A B h x y z q p;

assertnot [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_rhs A B h x y z q p
  ≡ @path_map_compositor_target_readable A B h x y z q p;

// A separately indexed q' is rejected at the retained formal endpoint.
assertnot [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q q' : τ (@= A y z))
  (p : τ (@= A x y)) ⊢
  @path_map_compositor_path A B h x y z q p
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p)
      (@path_map_compositor_rhs A B h x y z q' p));

// The next action remains a whole Functor between literal Path categories.
// Its generic fapp1_func therefore remains available for further iteration.
assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p0 p1 : τ (@= A x y)) ⊢
  @path_map_compositor_higher_func A B h x y z q p0 p1
  : τ (@Functor
      (@Path_cat (@= (@= A x y) p0 p1))
      (@Path_cat
        (@=
          (@= B (h x) (h z))
          (@path_map_compositor_lhs A B h x y z q p0)
          (@path_map_compositor_rhs A B h x y z q p1))));

assert [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p0 p1 : τ (@= A x y))
  (r : τ (@= (@= A x y) p0 p1)) ⊢
  @fapp0
    (@Path_cat (@= (@= A x y) p0 p1))
    (@Path_cat
      (@=
        (@= B (h x) (h z))
        (@path_map_compositor_lhs A B h x y z q p0)
        (@path_map_compositor_rhs A B h x y z q p1)))
    (@path_map_compositor_higher_func A B h x y z q p0 p1)
    r
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p0)
      (@path_map_compositor_rhs A B h x y z q p1));
