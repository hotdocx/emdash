/*
  Rule-free Path realization of the generic ordinary compositor.

  For a raw map h : A -> B, path_map_func(h) already carries the generic
  normal-lax compositor extracted from the displayed internal action.  Its
  codomain hom is a literal Path category, so the compositor is an equality
  between paths and ordinary path symmetry supplies its inverse.  This module
  retains the whole transformation and one next-hom action; it does not add a
  pseudofunctor classifier, compositor rule, inverse record, or second
  coherence hierarchy.

  The formal endpoint owners remain represented postcomposition.  Their
  conventional eq_ap/eq_trans readings are related propositionally through
  the existing generic proof-time postcomposition comparison followed by the
  J-derived path_comp_eq_trans theorem.  No readable endpoint is selected as
  a second runtime normal form.
*/

require open emdash.emdash3_2;

// Whole formal source of the compositor at a fixed second path q.
symbol path_map_compositor_lhs_func
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  (x : τ A)
  [y z : τ A]
  (q : τ (@= A y z))
  : τ (@Functor
      (@Hom_cat (Path_cat A) x y)
      (@Hom_cat (Path_cat B) (h x) (h z)))
≔ @functord_transport_lhs_func
    (Path_cat A)
    (@hom_ (Path_cat A) (Path_cat A) (@id_func (Path_cat A)) x)
    (@hom_
      (Path_cat B)
      (Path_cat A)
      (@path_map_func A B h)
      (h x))
    (@fapp1_at_transf
      (Path_cat A)
      (Path_cat B)
      (@path_map_func A B h)
      x)
    y z q;

// Whole formal target of the compositor at the same fixed path q.
symbol path_map_compositor_rhs_func
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  (x : τ A)
  [y z : τ A]
  (q : τ (@= A y z))
  : τ (@Functor
      (@Hom_cat (Path_cat A) x y)
      (@Hom_cat (Path_cat B) (h x) (h z)))
≔ @functord_transport_rhs_func
    (Path_cat A)
    (@hom_ (Path_cat A) (Path_cat A) (@id_func (Path_cat A)) x)
    (@hom_
      (Path_cat B)
      (Path_cat A)
      (@path_map_func A B h)
      (h x))
    (@fapp1_at_transf
      (Path_cat A)
      (Path_cat B)
      (@path_map_func A B h)
      x)
    y z q;

// Whole Path-realized compositor, still functorial in the first path p.
symbol path_map_compositor_transf
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  (x : τ A)
  [y z : τ A]
  (q : τ (@= A y z))
  : τ (Transf
      (@path_map_compositor_lhs_func A B h x y z q)
      (@path_map_compositor_rhs_func A B h x y z q))
≔ @tapp1_post_laxity_transf
    (Path_cat A)
    (Path_cat B)
    (@path_map_func A B h)
    (@path_map_func A B h)
    (@id (Functor_cat (Path_cat A) (Path_cat B)) (@path_map_func A B h))
    x y z q;

// Formal represented-postcomposition endpoint at p.
symbol path_map_compositor_lhs
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@= B (h x) (h z))
≔ @fapp0
    (@Hom_cat (Path_cat A) x y)
    (@Hom_cat (Path_cat B) (h x) (h z))
    (@path_map_compositor_lhs_func A B h x y z q)
    p;

// Formal represented-postcomposition target at p.
symbol path_map_compositor_rhs
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@= B (h x) (h z))
≔ @fapp0
    (@Hom_cat (Path_cat A) x y)
    (@Hom_cat (Path_cat B) (h x) (h z))
    (@path_map_compositor_rhs_func A B h x y z q)
    p;

// The generic directed compositor decodes directly to an equality of paths.
symbol path_map_compositor_path
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p)
      (@path_map_compositor_rhs A B h x y z q p))
≔ @fapp1_compositor
    (Path_cat A)
    (Path_cat B)
    (@path_map_func A B h)
    x y z q p;

// Path symmetry supplies the pseudo inverse; no independent inverse data is
// postulated.
symbol path_map_compositor_inverse
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_rhs A B h x y z q p)
      (@path_map_compositor_lhs A B h x y z q p))
≔ @eq_sym
    (@= B (h x) (h z))
    (@path_map_compositor_lhs A B h x y z q p)
    (@path_map_compositor_rhs A B h x y z q p)
    (@path_map_compositor_path A B h x y z q p);

// Conventional HoTT source: ap(h,p) followed by ap(h,q).
symbol path_map_compositor_source_readable
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@= B (h x) (h z))
≔ @eq_trans
    B (h x) (h y) (h z)
    (@eq_ap A B h x y p)
    (@eq_ap A B h y z q);

// Conventional HoTT target: ap(h,p followed by q).
symbol path_map_compositor_target_readable
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@= B (h x) (h z))
≔ @eq_ap A B h x z (@eq_trans A x y z p q);

// Reusable typed view: preserve both rigid generic heads while turning the
// active postcomposition proof-time comparison into equality evidence. Later
// Path and represented-associator specializations do not rely on transitive
// unification after projection.
symbol path_pseudo_laxity_postcomp_comp_path
  [A B : Cat]
  (F : τ (@Functor B A))
  (W : τ (@Obj A))
  [X Y : τ (@Obj B)]
  (h : τ (@Hom B X Y))
  (g : τ (@Hom A W (@fapp0 B A F X)))
  : τ (@=
      (@Hom A W (@fapp0 B A F Y))
      (@hom_postcomp_fapp0 A B F W X Y h g)
      (@comp_fapp0
        A W
        (@fapp0 B A F X)
        (@fapp0 B A F Y)
        (@fapp1_fapp0 B A F X Y h)
        g))
≔ @eq_refl
    (@Hom A W (@fapp0 B A F Y))
    (@hom_postcomp_fapp0 A B F W X Y h g);

// Represented path postcomposition agrees with J-derived transitivity by the
// selected E0 two-step route; this is propositional, not runtime conversion.
protected symbol path_pseudo_laxity_postcomp_eq_trans
  [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y))
  [z : τ A]
  (q : τ (@= A y z))
  : τ (@=
      (@= A x z)
      (@hom_postcomp_fapp0
        (Path_cat A)
        (Path_cat A)
        (@id_func (Path_cat A))
        x y z q p)
      (@eq_trans A x y z p q))
≔ @eq_trans
    (@= A x z)
    (@hom_postcomp_fapp0
      (Path_cat A)
      (Path_cat A)
      (@id_func (Path_cat A))
      x y z q p)
    (@comp_fapp0 (Path_cat A) x y z q p)
    (@eq_trans A x y z p q)
    (@path_pseudo_laxity_postcomp_comp_path
      (Path_cat A)
      (Path_cat A)
      (@id_func (Path_cat A))
      x y z q p)
    (@path_comp_eq_trans A x y p z q);

// The formal source agrees propositionally with its eq_ap/eq_trans reading.
symbol path_map_compositor_lhs_agrees_readable
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p)
      (@path_map_compositor_source_readable A B h x y z q p))
≔ @eq_trans
    (@= B (h x) (h z))
    (@path_map_compositor_lhs A B h x y z q p)
    (@comp_fapp0
      (Path_cat B)
      (h x) (h y) (h z)
      (@eq_ap A B h y z q)
      (@eq_ap A B h x y p))
    (@path_map_compositor_source_readable A B h x y z q p)
    (@path_pseudo_laxity_postcomp_comp_path
      (Path_cat B)
      (Path_cat A)
      (@path_map_func A B h)
      (h x)
      y z q
      (@eq_ap A B h x y p))
    (@path_comp_eq_trans
      B
      (h x) (h y)
      (@eq_ap A B h x y p)
      (h z)
      (@eq_ap A B h y z q));

// The formal target agrees propositionally with ap(h,p followed by q).
symbol path_map_compositor_rhs_agrees_readable
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_rhs A B h x y z q p)
      (@path_map_compositor_target_readable A B h x y z q p))
≔ @eq_ap
    (@= A x z)
    (@= B (h x) (h z))
    (λ r : τ (@= A x z), @eq_ap A B h x z r)
    (@hom_postcomp_fapp0
      (Path_cat A)
      (Path_cat A)
      (@id_func (Path_cat A))
      x y z q p)
    (@eq_trans A x y z p q)
    (@path_pseudo_laxity_postcomp_eq_trans A x y p z q);

// Internal first half of the endpoint change: readable source to formal
// target through the inverse source comparison and generic compositor.
protected symbol path_map_compositor_source_to_formal_rhs
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_source_readable A B h x y z q p)
      (@path_map_compositor_rhs A B h x y z q p))
≔ @eq_trans
    (@= B (h x) (h z))
    (@path_map_compositor_source_readable A B h x y z q p)
    (@path_map_compositor_lhs A B h x y z q p)
    (@path_map_compositor_rhs A B h x y z q p)
    (@eq_sym
      (@= B (h x) (h z))
      (@path_map_compositor_lhs A B h x y z q p)
      (@path_map_compositor_source_readable A B h x y z q p)
      (@path_map_compositor_lhs_agrees_readable A B h x y z q p))
    (@path_map_compositor_path A B h x y z q p);

// Readable pseudofunctoriality, assembled from the generic compositor and
// the two propositional endpoint comparisons above.
symbol path_map_compositor_readable
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_source_readable A B h x y z q p)
      (@path_map_compositor_target_readable A B h x y z q p))
≔ @eq_trans
    (@= B (h x) (h z))
    (@path_map_compositor_source_readable A B h x y z q p)
    (@path_map_compositor_rhs A B h x y z q p)
    (@path_map_compositor_target_readable A B h x y z q p)
    (@path_map_compositor_source_to_formal_rhs A B h x y z q p)
    (@path_map_compositor_rhs_agrees_readable A B h x y z q p);

// Canonical reverse of the readable path, again supplied by equality.
symbol path_map_compositor_readable_inverse
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p : τ (@= A x y))
  : τ (@=
      (@= B (h x) (h z))
      (@path_map_compositor_target_readable A B h x y z q p)
      (@path_map_compositor_source_readable A B h x y z q p))
≔ @eq_sym
    (@= B (h x) (h z))
    (@path_map_compositor_source_readable A B h x y z q p)
    (@path_map_compositor_target_readable A B h x y z q p)
    (@path_map_compositor_readable A B h x y z q p);

// One retained next-hom action.  It maps paths p0 = p1 to paths between the
// corresponding formal compositor endpoints and remains a whole Functor, so
// generic fapp1_func can iterate it further without a capped coherence head.
symbol path_map_compositor_higher_func
  [A B : Grpd]
  (h : τ (@Function_grpd A B))
  [x y z : τ A]
  (q : τ (@= A y z))
  (p0 p1 : τ (@= A x y))
  : τ (@Functor
      (@Hom_cat (@Hom_cat (Path_cat A) x y) p0 p1)
      (@Hom_cat
        (@Hom_cat (Path_cat B) (h x) (h z))
        (@path_map_compositor_lhs A B h x y z q p0)
        (@path_map_compositor_rhs A B h x y z q p1)))
≔ @tapp1_func
    (@Hom_cat (Path_cat A) x y)
    (@Hom_cat (Path_cat B) (h x) (h z))
    (@path_map_compositor_lhs_func A B h x y z q)
    (@path_map_compositor_rhs_func A B h x y z q)
    p0 p1
    (@path_map_compositor_transf A B h x y z q);
