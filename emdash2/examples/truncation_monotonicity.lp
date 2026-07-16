/*
  Reviewer example: one-step monotonicity of homotopy truncation levels.

  The -2 -> -1 base constructs contractible path spaces explicitly; higher
  levels recurse through the native TruncLevel eliminator. No proof erasure or
  global weakening rewrite is selected.
*/

require open emdash.emdash3_2;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (@= A x y)) ⊢
  @eq_sym_trans_self A x y p
  : τ (@=
      (@= A y y)
      (@eq_trans A y x y (@eq_sym A x y p) p)
      (@eq_refl A y));

assert [A : Grpd]
  (c : τ (IsContr A)) ⊢
  @is_contr_is_prop A c
  : τ (IsPropGrpd A);

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd n A)) ⊢
  @is_trunc_grpd_succ n A h
  : τ (IsTruncGrpd (trunc_succ n) A);

assert [A : Grpd]
  (h : τ (IsContr A)) ⊢
  @is_trunc_grpd_succ trunc_minus_two A h
  ≡ @is_contr_is_prop A h;

assert (n : TruncLevel)
  [A : Grpd]
  (h : τ (IsTruncGrpd (trunc_succ n) A))
  (x y : τ A) ⊢
  @is_trunc_grpd_succ (trunc_succ n) A h x y
  ≡ @is_trunc_grpd_succ n (@= A x y) (h x y);

assert [A : Grpd]
  (h : τ (IsContr A)) ⊢
  @is_trunc_grpd_succ trunc_minus_two A h
  : τ (IsPropGrpd A);

assert [A : Grpd]
  (h : τ (IsPropGrpd A)) ⊢
  @is_trunc_grpd_succ trunc_minus_one A h
  : τ (IsSetGrpd A);

assert [A : Grpd]
  (h : τ (IsSetGrpd A)) ⊢
  @is_trunc_grpd_succ trunc_zero A h
  : τ (IsGroupoidGrpd A);

assertnot [A : Grpd]
  (c : τ (IsContr A))
  (x : τ A) ⊢
  @contractible_path_center A c x x
  ≡ @eq_refl A x;
