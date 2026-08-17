/*
  Mere connectedness of the groupoidal Circle through computational
  propositional truncation.

  The fibre over x is ||circle_base = x||_{-1}. Its retained proposition
  evidence supplies the generating-loop PathOver, so dependent Circle
  induction constructs mere connectedness without choosing a path globally.
  Eliminating that evidence into the set truncation then proves the latter
  contractible, without replacing its carrier judgmentally by Unit.
*/

require open emdash.emdash3_2_truncation_reflector;
require open emdash.emdash3_2_circle_hit;

symbol CircleConnected
  (x : τ Circle_grpd)
  : Grpd
≔ @Trunc_grpd
    trunc_minus_one
    (@= Circle_grpd circle_base x);

symbol circle_connected_fibre_is_prop
  (x : τ Circle_grpd)
  : τ (IsPropGrpd (@CircleConnected x))
≔ @trunc_ntype_is_truncated
    trunc_minus_one
    (@= Circle_grpd circle_base x);

symbol circle_connected_base
  : τ (@CircleConnected circle_base)
≔ @trunc_intro
    trunc_minus_one
    (@= Circle_grpd circle_base circle_base)
    (@eq_refl Circle_grpd circle_base);

// Propositional fibres supply the unique dependent loop datum.
symbol circle_connected_loop_coherence
  : τ (@PathOver
      Circle_grpd
      CircleConnected
      circle_base circle_base circle_loop
      circle_connected_base
      circle_connected_base)
≔ @prop_family_pathover
    Circle_grpd
    CircleConnected
    circle_connected_fibre_is_prop
    circle_base circle_base circle_loop
    circle_connected_base
    circle_connected_base;

symbol circle_connected
  (x : τ Circle_grpd)
  : τ (@CircleConnected x)
≔ @circle_ind
    CircleConnected
    circle_connected_base
    circle_connected_loop_coherence
    x;

/*
  Conditional Circle consumer: the set truncation is contractible.

  Mere based connectedness first yields a path between the corresponding
  points of the set truncation. Set-truncation induction then extends that
  path to every point. Contractibility is retained as evidence; the carrier
  is not judgmentally replaced by Unit.
*/

symbol CircleSetTrunc_grpd
  : Grpd
≔ @Trunc_grpd trunc_zero Circle_grpd;

symbol circle_set_trunc_center
  : τ CircleSetTrunc_grpd
≔ @trunc_intro trunc_zero Circle_grpd circle_base;

symbol circle_set_trunc_intro_path
  [x : τ Circle_grpd]
  (p : τ (@= Circle_grpd circle_base x))
  : τ (@=
      CircleSetTrunc_grpd
      circle_set_trunc_center
      (@trunc_intro trunc_zero Circle_grpd x))
≔ @eq_ap
    Circle_grpd
    CircleSetTrunc_grpd
    (λ y : τ Circle_grpd,
      @trunc_intro trunc_zero Circle_grpd y)
    circle_base x p;

// Eliminate mere connectedness into a path of the set truncation.
symbol circle_set_trunc_center_path_at_intro
  (x : τ Circle_grpd)
  : τ (@=
      CircleSetTrunc_grpd
      circle_set_trunc_center
      (@trunc_intro trunc_zero Circle_grpd x))
≔ @trunc_rec_ambient
    trunc_minus_one
    (@= Circle_grpd circle_base x)
    (@=
      CircleSetTrunc_grpd
      circle_set_trunc_center
      (@trunc_intro trunc_zero Circle_grpd x))
    ((@trunc_ntype_is_truncated trunc_zero Circle_grpd)
      circle_set_trunc_center
      (@trunc_intro trunc_zero Circle_grpd x))
    (λ p : τ (@= Circle_grpd circle_base x),
      @circle_set_trunc_intro_path x p)
    (@circle_connected x);

// Extend the constructor case to every point of the set truncation.
symbol circle_set_trunc_contract
  (z : τ CircleSetTrunc_grpd)
  : τ (@=
      CircleSetTrunc_grpd
      circle_set_trunc_center
      z)
≔ @trunc_ind_ambient
    trunc_zero
    Circle_grpd
    (λ z : τ CircleSetTrunc_grpd,
      @= CircleSetTrunc_grpd circle_set_trunc_center z)
    (λ z : τ CircleSetTrunc_grpd,
      @is_trunc_path_same_level
        trunc_zero
        CircleSetTrunc_grpd
        (@trunc_ntype_is_truncated trunc_zero Circle_grpd)
        circle_set_trunc_center z)
    circle_set_trunc_center_path_at_intro
    z;

symbol circle_set_trunc_is_contr
  : τ (IsContr CircleSetTrunc_grpd)
≔ @Struct_sigma
    CircleSetTrunc_grpd
    (λ centre : τ CircleSetTrunc_grpd,
      @Pi_grpd CircleSetTrunc_grpd
        (λ z : τ CircleSetTrunc_grpd,
          @= CircleSetTrunc_grpd centre z))
    circle_set_trunc_center
    circle_set_trunc_contract;
