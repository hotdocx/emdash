/*
  Explicit composition action of the generic groupoidification unit.

  For arbitrary composable arrows f and g in C, the whole unit carries the
  ordinary normal-lax compositor extracted by the existing internal-action
  calculus.  Its codomain is Path_cat(Groupoidify(C)), so this cell is
  groupoidal.  The historical strict endpoint cuts may make its displayed
  endpoints convertible, but they do not reduce this explicit cell to an
  identity.

  The whole transformation and one next hom action are retained here.  No
  constructor-specific composition rule or duplicate coherence hierarchy is
  introduced.
*/

require open emdash.emdash3_2_groupoidification_hit;

// Formal source of the unit compositor at a fixed second arrow g.
symbol groupoidify_unit_compositor_lhs_func
  [C : Cat]
  (x : τ (Obj C))
  [y z : τ (Obj C)]
  (g : τ (Hom C y z))
  : τ (@Functor
      (@Hom_cat C x y)
      (@Hom_cat
        (Path_cat (@Groupoidify C))
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x)
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) z)))
≔ @functord_transport_lhs_func
    C
    (@hom_ C C (@id_func C) x)
    (@hom_
      (Path_cat (@Groupoidify C))
      C
      (@groupoidify_unit_func C)
      (@fapp0 C (Path_cat (@Groupoidify C))
        (@groupoidify_unit_func C) x))
    (@fapp1_at_transf
      C (Path_cat (@Groupoidify C))
      (@groupoidify_unit_func C) x)
    y z g;

// Formal target of the same unit compositor.
symbol groupoidify_unit_compositor_rhs_func
  [C : Cat]
  (x : τ (Obj C))
  [y z : τ (Obj C)]
  (g : τ (Hom C y z))
  : τ (@Functor
      (@Hom_cat C x y)
      (@Hom_cat
        (Path_cat (@Groupoidify C))
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x)
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) z)))
≔ @functord_transport_rhs_func
    C
    (@hom_ C C (@id_func C) x)
    (@hom_
      (Path_cat (@Groupoidify C))
      C
      (@groupoidify_unit_func C)
      (@fapp0 C (Path_cat (@Groupoidify C))
        (@groupoidify_unit_func C) x))
    (@fapp1_at_transf
      C (Path_cat (@Groupoidify C))
      (@groupoidify_unit_func C) x)
    y z g;

// Whole compositor, natural in the first arrow f.
symbol groupoidify_unit_compositor_transf
  [C : Cat]
  (x : τ (Obj C))
  [y z : τ (Obj C)]
  (g : τ (Hom C y z))
  : τ (@Transf
      (@Hom_cat C x y)
      (@Hom_cat
        (Path_cat (@Groupoidify C))
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x)
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) z))
      (@groupoidify_unit_compositor_lhs_func C x y z g)
      (@groupoidify_unit_compositor_rhs_func C x y z g))
≔ @tapp1_post_laxity_transf
    C
    (Path_cat (@Groupoidify C))
    (@groupoidify_unit_func C)
    (@groupoidify_unit_func C)
    (@id
      (@Functor_cat C (Path_cat (@Groupoidify C)))
      (@groupoidify_unit_func C))
    x y z g;

// Point component: the existing generic ordinary compositor.
symbol groupoidify_unit_compositor
  [C : Cat]
  [x y z : τ (Obj C)]
  (g : τ (Hom C y z))
  (f : τ (Hom C x y))
  : τ (@Hom
      (@Hom_cat
        (Path_cat (@Groupoidify C))
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) x)
        (@fapp0 C (Path_cat (@Groupoidify C))
          (@groupoidify_unit_func C) z))
      (@fapp0
        (@Hom_cat C x y)
        (@Hom_cat
          (Path_cat (@Groupoidify C))
          (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) x)
          (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) z))
        (@groupoidify_unit_compositor_lhs_func C x y z g)
        f)
      (@fapp0
        (@Hom_cat C x y)
        (@Hom_cat
          (Path_cat (@Groupoidify C))
          (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) x)
          (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) z))
        (@groupoidify_unit_compositor_rhs_func C x y z g)
        f))
≔ @fapp1_compositor
    C (Path_cat (@Groupoidify C))
    (@groupoidify_unit_func C)
    x y z g f;

// One retained next action of the same whole compositor.
symbol groupoidify_unit_compositor_next_func
  [C : Cat]
  [x y z : τ (Obj C)]
  (g : τ (Hom C y z))
  (f0 f1 : τ (Hom C x y))
  : τ (@Functor
      (@Hom_cat (@Hom_cat C x y) f0 f1)
      (@Hom_cat
        (@Hom_cat
          (Path_cat (@Groupoidify C))
          (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) x)
          (@fapp0 C (Path_cat (@Groupoidify C))
            (@groupoidify_unit_func C) z))
        (@fapp0
          (@Hom_cat C x y)
          (@Hom_cat
            (Path_cat (@Groupoidify C))
            (@fapp0 C (Path_cat (@Groupoidify C))
              (@groupoidify_unit_func C) x)
            (@fapp0 C (Path_cat (@Groupoidify C))
              (@groupoidify_unit_func C) z))
          (@groupoidify_unit_compositor_lhs_func C x y z g)
          f0)
        (@fapp0
          (@Hom_cat C x y)
          (@Hom_cat
            (Path_cat (@Groupoidify C))
            (@fapp0 C (Path_cat (@Groupoidify C))
              (@groupoidify_unit_func C) x)
            (@fapp0 C (Path_cat (@Groupoidify C))
              (@groupoidify_unit_func C) z))
          (@groupoidify_unit_compositor_rhs_func C x y z g)
          f1)))
≔ @tapp1_func
    (@Hom_cat C x y)
    (@Hom_cat
      (Path_cat (@Groupoidify C))
      (@fapp0 C (Path_cat (@Groupoidify C))
        (@groupoidify_unit_func C) x)
      (@fapp0 C (Path_cat (@Groupoidify C))
        (@groupoidify_unit_func C) z))
    (@groupoidify_unit_compositor_lhs_func C x y z g)
    (@groupoidify_unit_compositor_rhs_func C x y z g)
    f0 f1
    (@groupoidify_unit_compositor_transf C x y z g);
