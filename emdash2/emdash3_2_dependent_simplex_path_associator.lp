/*
  Groupoidal source associator from represented dependent-hom action.

  The ordinary represented functor

    Rep_catd_func(Z) : Op_cat(Z) -> Catd_cat(Z)

  carries the generic normal-lax compositor already extracted from the whole
  internal action.  Evaluating that displayed compositor at a fourth object
  and arrow gives a directed associator cell.  For Z = Path_cat(A), its target
  hom is again a Path category, so the cell is an invertible equality.

  The formal endpoints deliberately retain the existing represented
  pre/postcomposition owners. Typed equality bridges join them propositionally
  to `(h o g) o f` and `h o (g o f)` for arbitrary Z; equality-induced arrows
  conjugate the whole cell to those raw endpoints. In a Path target this cell
  is an invertible equality. No runtime rule, unifier, generic reassociation
  equation, proof-irrelevance principle, or duplicate coherence record is
  added. One next action remains public.
*/

require open emdash.emdash3_2_path_pseudo_laxity;

// Direct J-derived categorical Path associativity, independent of comp_assoc.
symbol path_cat_assoc_J
  [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z))
  : τ (@=
      (@= A w z)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f))
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f))
≔ (@ind_eqr
      A x
      (λ w0 : τ A,
        λ f0 : τ (@= A w0 x),
          @Pi_grpd A
            (λ y0 : τ A,
              @Pi_grpd
                (@= A x y0)
                (λ g0 : τ (@= A x y0),
                  @Pi_grpd A
                    (λ z0 : τ A,
                      @Pi_grpd
                        (@= A y0 z0)
                        (λ h0 : τ (@= A y0 z0),
                          @=
                            (@= A w0 z0)
                            (@comp_fapp0
                              (Path_cat A) w0 y0 z0 h0
                              (@comp_fapp0
                                (Path_cat A) w0 x y0 g0 f0))
                            (@comp_fapp0
                              (Path_cat A) w0 x z0
                              (@comp_fapp0
                                (Path_cat A) x y0 z0 h0 g0)
                              f0))))))
      (λ y0 : τ A,
        λ g0 : τ (@= A x y0),
          λ z0 : τ A,
            λ h0 : τ (@= A y0 z0),
              @eq_refl
                (@= A x z0)
                (@comp_fapp0 (Path_cat A) x y0 z0 h0 g0))
      w f)
    y g z h;

// Formal source displayed functor of the represented compositor.
symbol represented_assoc_lhs_funcd
  [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  : τ (Functord (@Rep_catd Z x2) (@Rep_catd Z x0))
≔ @fapp0
    (@Hom_cat (Op_cat Z) x2 x1)
    (@Hom_cat
      (@Catd_cat Z)
      (@Rep_catd Z x2)
      (@Rep_catd Z x0))
    (@functord_transport_lhs_func
      (Op_cat Z)
      (@hom_ (Op_cat Z) (Op_cat Z) (@id_func (Op_cat Z)) x2)
      (@hom_
        (@Catd_cat Z)
        (Op_cat Z)
        (@Rep_catd_func Z)
        (@Rep_catd Z x2))
      (@fapp1_at_transf
        (Op_cat Z)
        (@Catd_cat Z)
        (@Rep_catd_func Z)
        x2)
      x1 x0 f)
    g;

// Formal target displayed functor of the represented compositor.
symbol represented_assoc_rhs_funcd
  [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  : τ (Functord (@Rep_catd Z x2) (@Rep_catd Z x0))
≔ @fapp0
    (@Hom_cat (Op_cat Z) x2 x1)
    (@Hom_cat
      (@Catd_cat Z)
      (@Rep_catd Z x2)
      (@Rep_catd Z x0))
    (@functord_transport_rhs_func
      (Op_cat Z)
      (@hom_ (Op_cat Z) (Op_cat Z) (@id_func (Op_cat Z)) x2)
      (@hom_
        (@Catd_cat Z)
        (Op_cat Z)
        (@Rep_catd_func Z)
        (@Rep_catd Z x2))
      (@fapp1_at_transf
        (Op_cat Z)
        (@Catd_cat Z)
        (@Rep_catd_func Z)
        x2)
      x1 x0 f)
    g;

// Whole displayed represented associator before any point projection.
symbol represented_assoc_transfd
  [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  : τ (Transfd
      (@represented_assoc_lhs_funcd Z x0 x1 x2 f g)
      (@represented_assoc_rhs_funcd Z x0 x1 x2 f g))
≔ @fapp1_compositor
    (Op_cat Z)
    (@Catd_cat Z)
    (@Rep_catd_func Z)
    x2 x1 x0 f g;

// Exact formal source of the component at x3,h.
symbol represented_assoc_lhs
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (Hom Z x0 x3)
≔ @fapp0
    (@Fibre_cat Z (@Rep_catd Z x2) x3)
    (@Fibre_cat Z (@Rep_catd Z x0) x3)
    (@Fibre_func
      Z
      (@Rep_catd Z x2)
      (@Rep_catd Z x0)
      (@represented_assoc_lhs_funcd Z x0 x1 x2 f g)
      x3)
    h;

// Exact formal target of the component at x3,h.
symbol represented_assoc_rhs
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (Hom Z x0 x3)
≔ @fapp0
    (@Fibre_cat Z (@Rep_catd Z x2) x3)
    (@Fibre_cat Z (@Rep_catd Z x0) x3)
    (@Fibre_func
      Z
      (@Rep_catd Z x2)
      (@Rep_catd Z x0)
      (@represented_assoc_rhs_funcd Z x0 x1 x2 f g)
      x3)
    h;

// Formal component of the whole represented compositor.
symbol represented_assoc_cell
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (Hom
      (Hom_cat Z x0 x3)
      (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
      (@represented_assoc_rhs Z x0 x1 x2 x3 f g h))
≔ @Fibre_transf_app
    Z
    (@Rep_catd Z x2)
    (@Rep_catd Z x0)
    (@represented_assoc_lhs_funcd Z x0 x1 x2 f g)
    (@represented_assoc_rhs_funcd Z x0 x1 x2 f g)
    (@represented_assoc_transfd Z x0 x1 x2 f g)
    x3 h;

// Retained next action of the represented component in the final arrow.
symbol represented_assoc_higher_func
  [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (x3 : τ (Obj Z))
  (h0 h1 : τ (Hom Z x2 x3))
  : τ (Functor
      (Hom_cat (Hom_cat Z x2 x3) h0 h1)
      (Hom_cat
        (Hom_cat Z x0 x3)
        (@represented_assoc_lhs Z x0 x1 x2 x3 f g h0)
        (@represented_assoc_rhs Z x0 x1 x2 x3 f g h1)))
≔ @tapp1_func
    (@Fibre_cat Z (@Rep_catd Z x2) x3)
    (@Fibre_cat Z (@Rep_catd Z x0) x3)
    (@Fibre_func
      Z
      (@Rep_catd Z x2)
      (@Rep_catd Z x0)
      (@represented_assoc_lhs_funcd Z x0 x1 x2 f g)
      x3)
    (@Fibre_func
      Z
      (@Rep_catd Z x2)
      (@Rep_catd Z x0)
      (@represented_assoc_rhs_funcd Z x0 x1 x2 f g)
      x3)
    h0 h1
    (@Fibre_transf
      Z
      (@Rep_catd Z x2)
      (@Rep_catd Z x0)
      (@represented_assoc_lhs_funcd Z x0 x1 x2 f g)
      (@represented_assoc_rhs_funcd Z x0 x1 x2 f g)
      (@represented_assoc_transfd Z x0 x1 x2 f g)
      x3);

// Precomposition's stable point owner agrees propositionally with raw comp.
protected symbol represented_assoc_precomp_comp_path
  [Z : Cat]
  [w x y : τ (Obj Z)]
  (f : τ (Hom Z w x))
  (g : τ (Hom Z x y))
  : τ (@=
      (Hom Z w y)
      (@hom_precomp_along_fapp0
        Z Z (@id_func Z) y w x f g)
      (@comp_fapp0 Z w x y g f))
≔ @eq_refl
    (Hom Z w y)
    (@hom_precomp_along_fapp0
      Z Z (@id_func Z) y w x f g);

// Opposite represented base composite agrees with the ordinary g o f.
protected symbol represented_assoc_base_comp_path
  [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  : τ (@=
      (Hom Z x0 x2)
      (@hom_postcomp_fapp0
        (Op_cat Z)
        (Op_cat Z)
        (@id_func (Op_cat Z))
        x2 x1 x0 f g)
      (@comp_fapp0 Z x0 x1 x2 g f))
≔ @path_pseudo_laxity_postcomp_comp_path
    (Op_cat Z)
    (Op_cat Z)
    (@id_func (Op_cat Z))
    x2 x1 x0 f g;

// Whole represented source agrees with the composite of its two actions.
symbol represented_assoc_lhs_funcd_agrees_comp
  [Z : Cat]
  [x0 x1 x2 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  : τ (@=
      (@Functord Z (@Rep_catd Z x2) (@Rep_catd Z x0))
      (@represented_assoc_lhs_funcd Z x0 x1 x2 f g)
      (@comp_catd_fapp0
        Z
        (@Rep_catd Z x2)
        (@Rep_catd Z x1)
        (@Rep_catd Z x0)
        (@hom_int_precomp_func Z Z (@id_func Z) x1 x0 f)
        (@hom_int_precomp_func Z Z (@id_func Z) x2 x1 g)))
≔ @path_pseudo_laxity_postcomp_comp_path
    (@Catd_cat Z)
    (Op_cat Z)
    (@Rep_catd_func Z)
    (@Rep_catd Z x2)
    x1 x0 f
    (@hom_int_precomp_func Z Z (@id_func Z) x2 x1 g);

// Component of that displayed composite is nested precomposition.
protected symbol represented_assoc_comp_component_path
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (@=
      (Hom Z x0 x3)
      (@fapp0
        (@Fibre_cat Z (@Rep_catd Z x2) x3)
        (@Fibre_cat Z (@Rep_catd Z x0) x3)
        (@Fibre_func
          Z
          (@Rep_catd Z x2)
          (@Rep_catd Z x0)
          (@comp_catd_fapp0
            Z
            (@Rep_catd Z x2)
            (@Rep_catd Z x1)
            (@Rep_catd Z x0)
            (@hom_int_precomp_func Z Z (@id_func Z) x1 x0 f)
            (@hom_int_precomp_func Z Z (@id_func Z) x2 x1 g))
          x3)
        h)
      (@hom_precomp_along_fapp0
        Z Z (@id_func Z) x3 x0 x1 f
        (@hom_precomp_along_fapp0
          Z Z (@id_func Z) x3 x1 x2 g h)))
≔ @eq_refl
    (Hom Z x0 x3)
    (@fapp0
      (@Fibre_cat Z (@Rep_catd Z x2) x3)
      (@Fibre_cat Z (@Rep_catd Z x0) x3)
      (@Fibre_func
        Z
        (@Rep_catd Z x2)
        (@Rep_catd Z x0)
        (@comp_catd_fapp0
          Z
          (@Rep_catd Z x2)
          (@Rep_catd Z x1)
          (@Rep_catd Z x0)
          (@hom_int_precomp_func Z Z (@id_func Z) x1 x0 f)
          (@hom_int_precomp_func Z Z (@id_func Z) x2 x1 g))
        x3)
      h);

// Generic formal source agrees with `(h o g) o f` without associativity.
symbol represented_assoc_lhs_agrees_raw
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (@=
      (Hom Z x0 x3)
      (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
      (@comp_fapp0
        Z x0 x1 x3
        (@comp_fapp0 Z x1 x2 x3 h g)
        f))
≔ @eq_trans
    (Hom Z x0 x3)
    (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
    (@fapp0
      (@Fibre_cat Z (@Rep_catd Z x2) x3)
      (@Fibre_cat Z (@Rep_catd Z x0) x3)
      (@Fibre_func
        Z
        (@Rep_catd Z x2)
        (@Rep_catd Z x0)
        (@comp_catd_fapp0
          Z
          (@Rep_catd Z x2)
          (@Rep_catd Z x1)
          (@Rep_catd Z x0)
          (@hom_int_precomp_func Z Z (@id_func Z) x1 x0 f)
          (@hom_int_precomp_func Z Z (@id_func Z) x2 x1 g))
        x3)
      h)
    (@comp_fapp0
      Z x0 x1 x3
      (@comp_fapp0 Z x1 x2 x3 h g)
      f)
    (@eq_ap
      (@Functord Z (@Rep_catd Z x2) (@Rep_catd Z x0))
      (Hom Z x0 x3)
      (λ FF : τ (@Functord Z (@Rep_catd Z x2) (@Rep_catd Z x0)),
        @fapp0
          (@Fibre_cat Z (@Rep_catd Z x2) x3)
          (@Fibre_cat Z (@Rep_catd Z x0) x3)
          (@Fibre_func Z (@Rep_catd Z x2) (@Rep_catd Z x0) FF x3)
          h)
      _ _
      (@represented_assoc_lhs_funcd_agrees_comp Z x0 x1 x2 f g))
    (@eq_trans
      (Hom Z x0 x3)
      (@fapp0
        (@Fibre_cat Z (@Rep_catd Z x2) x3)
        (@Fibre_cat Z (@Rep_catd Z x0) x3)
        (@Fibre_func
          Z
          (@Rep_catd Z x2)
          (@Rep_catd Z x0)
          (@comp_catd_fapp0
            Z
            (@Rep_catd Z x2)
            (@Rep_catd Z x1)
            (@Rep_catd Z x0)
            (@hom_int_precomp_func Z Z (@id_func Z) x1 x0 f)
            (@hom_int_precomp_func Z Z (@id_func Z) x2 x1 g))
          x3)
        h)
      (@hom_precomp_along_fapp0
        Z Z (@id_func Z) x3 x0 x1 f
        (@hom_precomp_along_fapp0
          Z Z (@id_func Z) x3 x1 x2 g h))
      (@comp_fapp0
        Z x0 x1 x3
        (@comp_fapp0 Z x1 x2 x3 h g)
        f)
      (@represented_assoc_comp_component_path Z x0 x1 x2 x3 f g h)
      (@eq_trans
        (Hom Z x0 x3)
        (@hom_precomp_along_fapp0
          Z Z (@id_func Z) x3 x0 x1 f
          (@hom_precomp_along_fapp0
            Z Z (@id_func Z) x3 x1 x2 g h))
        (@hom_precomp_along_fapp0
          Z Z (@id_func Z) x3 x0 x1 f
          (@comp_fapp0 Z x1 x2 x3 h g))
        (@comp_fapp0
          Z x0 x1 x3
          (@comp_fapp0 Z x1 x2 x3 h g)
          f)
        (@eq_ap
          (Hom Z x1 x3)
          (Hom Z x0 x3)
          (λ q : τ (Hom Z x1 x3),
            @hom_precomp_along_fapp0
              Z Z (@id_func Z) x3 x0 x1 f q)
          _ _
          (@represented_assoc_precomp_comp_path Z x1 x2 x3 g h))
        (@represented_assoc_precomp_comp_path
          Z x0 x1 x3 f
          (@comp_fapp0 Z x1 x2 x3 h g))));

// Generic formal target agrees with `h o (g o f)`.
symbol represented_assoc_rhs_agrees_raw
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (@=
      (Hom Z x0 x3)
      (@represented_assoc_rhs Z x0 x1 x2 x3 f g h)
      (@comp_fapp0
        Z x0 x2 x3 h
        (@comp_fapp0 Z x0 x1 x2 g f)))
≔ @eq_trans
    (Hom Z x0 x3)
    (@represented_assoc_rhs Z x0 x1 x2 x3 f g h)
    (@hom_precomp_along_fapp0
      Z Z (@id_func Z) x3 x0 x2
      (@comp_fapp0 Z x0 x1 x2 g f)
      h)
    (@comp_fapp0
      Z x0 x2 x3 h
      (@comp_fapp0 Z x0 x1 x2 g f))
    (@eq_ap
      (Hom Z x0 x2)
      (Hom Z x0 x3)
      (λ k : τ (Hom Z x0 x2),
        @hom_precomp_along_fapp0
          Z Z (@id_func Z) x3 x0 x2 k h)
      _ _
      (@represented_assoc_base_comp_path Z x0 x1 x2 f g))
    (@represented_assoc_precomp_comp_path
      Z x0 x2 x3
      (@comp_fapp0 Z x0 x1 x2 g f)
      h);

// Directed represented associator at literal raw-composition endpoints.
symbol represented_assoc_readable_cell
  [Z : Cat]
  [x0 x1 x2 x3 : τ (Obj Z)]
  (f : τ (Hom Z x0 x1))
  (g : τ (Hom Z x1 x2))
  (h : τ (Hom Z x2 x3))
  : τ (Hom
      (Hom_cat Z x0 x3)
      (@comp_fapp0
        Z x0 x1 x3
        (@comp_fapp0 Z x1 x2 x3 h g)
        f)
      (@comp_fapp0
        Z x0 x2 x3 h
        (@comp_fapp0 Z x0 x1 x2 g f)))
≔ @comp_fapp0
    (Hom_cat Z x0 x3)
    (@comp_fapp0
      Z x0 x1 x3
      (@comp_fapp0 Z x1 x2 x3 h g)
      f)
    (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
    (@comp_fapp0
      Z x0 x2 x3 h
      (@comp_fapp0 Z x0 x1 x2 g f))
    (@comp_fapp0
      (Hom_cat Z x0 x3)
      (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
      (@represented_assoc_rhs Z x0 x1 x2 x3 f g h)
      (@comp_fapp0
        Z x0 x2 x3 h
        (@comp_fapp0 Z x0 x1 x2 g f))
      (@path_to_hom
        (Hom_cat Z x0 x3)
        (@represented_assoc_rhs Z x0 x1 x2 x3 f g h)
        (@comp_fapp0
          Z x0 x2 x3 h
          (@comp_fapp0 Z x0 x1 x2 g f))
        (@represented_assoc_rhs_agrees_raw Z x0 x1 x2 x3 f g h))
      (@represented_assoc_cell Z x0 x1 x2 x3 f g h))
    (@path_to_hom
      (Hom_cat Z x0 x3)
      (@comp_fapp0
        Z x0 x1 x3
        (@comp_fapp0 Z x1 x2 x3 h g)
        f)
      (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
      (@eq_sym
        (Hom Z x0 x3)
        (@represented_assoc_lhs Z x0 x1 x2 x3 f g h)
        (@comp_fapp0
          Z x0 x1 x3
          (@comp_fapp0 Z x1 x2 x3 h g)
          f)
        (@represented_assoc_lhs_agrees_raw Z x0 x1 x2 x3 f g h)));

// Path aliases of the generic endpoint comparisons.
symbol path_represented_assoc_lhs_agrees
  [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z))
  : τ (@=
      (@= A w z)
      (@represented_assoc_lhs (Path_cat A) w x y z f g h)
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f))
≔ @represented_assoc_lhs_agrees_raw
    (Path_cat A) w x y z f g h;

symbol path_represented_assoc_rhs_agrees
  [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z))
  : τ (@=
      (@= A w z)
      (@represented_assoc_rhs (Path_cat A) w x y z f g h)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f)))
≔ @represented_assoc_rhs_agrees_raw
    (Path_cat A) w x y z f g h;

// Readable represented associator in the groupoidal Path profile.
symbol path_represented_assoc
  [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z))
  : τ (@=
      (@= A w z)
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f)))
≔ @eq_trans
    (@= A w z)
    (@comp_fapp0
      (Path_cat A) w x z
      (@comp_fapp0 (Path_cat A) x y z h g)
      f)
    (@represented_assoc_lhs (Path_cat A) w x y z f g h)
    (@comp_fapp0
      (Path_cat A) w y z h
      (@comp_fapp0 (Path_cat A) w x y g f))
    (@eq_sym
      (@= A w z)
      (@represented_assoc_lhs (Path_cat A) w x y z f g h)
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f)
      (@path_represented_assoc_lhs_agrees A w x f y g z h))
    (@eq_trans
      (@= A w z)
      (@represented_assoc_lhs (Path_cat A) w x y z f g h)
      (@represented_assoc_rhs (Path_cat A) w x y z f g h)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f))
      (@represented_assoc_cell (Path_cat A) w x y z f g h)
      (@path_represented_assoc_rhs_agrees A w x f y g z h));

// Direct J presentation in the same forward orientation; proof terms remain
// intentionally distinct from the represented-action construction.
symbol path_assoc_J_forward
  [A : Grpd]
  [w x : τ A]
  (f : τ (@= A w x))
  [y : τ A]
  (g : τ (@= A x y))
  [z : τ A]
  (h : τ (@= A y z))
  : τ (@=
      (@= A w z)
      (@comp_fapp0
        (Path_cat A) w x z
        (@comp_fapp0 (Path_cat A) x y z h g)
        f)
      (@comp_fapp0
        (Path_cat A) w y z h
        (@comp_fapp0 (Path_cat A) w x y g f)))
≔ @eq_sym
    (@= A w z)
    (@comp_fapp0
      (Path_cat A) w y z h
      (@comp_fapp0 (Path_cat A) w x y g f))
    (@comp_fapp0
      (Path_cat A) w x z
      (@comp_fapp0 (Path_cat A) x y z h g)
      f)
    (@path_cat_assoc_J A w x f y g z h);
