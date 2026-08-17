/*
  Focused reviewer for mere based connectedness of the Circle.

  Propositional truncation makes the based-path family proposition-valued,
  so Circle induction needs no chosen untruncated global path.
*/

require open emdash.emdash3_2_circle_connectedness;

assert (x : τ Circle_grpd) ⊢
  @CircleConnected x
  ≡ @Trunc_grpd trunc_minus_one (@= Circle_grpd circle_base x);

assert (x : τ Circle_grpd) ⊢
  @circle_connected_fibre_is_prop x
  : τ (IsPropGrpd (@CircleConnected x));

assert ⊢
  circle_connected_loop_coherence
  : τ (@PathOver
      Circle_grpd
      CircleConnected
      circle_base circle_base circle_loop
      circle_connected_base
      circle_connected_base);

assert (x : τ Circle_grpd) ⊢
  @circle_connected x
  : τ (@CircleConnected x);

// Point computation is inherited from the Circle eliminator.
assert ⊢
  @circle_connected circle_base
  ≡ @trunc_intro
      trunc_minus_one
      (@= Circle_grpd circle_base circle_base)
      (@eq_refl Circle_grpd circle_base);

// Mere connectedness does not choose an untruncated global based path.
assertnot (x : τ Circle_grpd) ⊢
  @circle_connected x
  : τ (@= Circle_grpd circle_base x);

// The dependent endpoint remains visible.
assertnot (x y : τ Circle_grpd) ⊢
  @circle_connected x
  : τ (@CircleConnected y);

// Mere connectedness contracts the set truncation of the Circle.
assert ⊢
  circle_set_trunc_is_contr
  : τ (IsContr (@Trunc_grpd trunc_zero Circle_grpd));

assert ⊢
  @is_contr_center
    CircleSetTrunc_grpd
    circle_set_trunc_is_contr
  ≡ @trunc_intro trunc_zero Circle_grpd circle_base;

assert ⊢
  @circle_set_trunc_center_path_at_intro circle_base
  ≡ @eq_refl
      CircleSetTrunc_grpd
      circle_set_trunc_center;

assert ⊢
  @circle_set_trunc_contract circle_set_trunc_center
  ≡ @eq_refl
      CircleSetTrunc_grpd
      circle_set_trunc_center;

// Contractibility is evidence, not a judgmental replacement by Unit.
assertnot ⊢
  CircleSetTrunc_grpd
  ≡ Unit_grpd;
