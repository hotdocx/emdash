/*
  Reviewer milestone: path categories.

  This demonstrates that equality/path data is internalized as a category:
  objects are points, homs are path categories, identities are reflexivity,
  and shared categorical composition agrees propositionally with J-derived
  path transitivity. Path reversal is the arrow action of a functor from the
  genuine opposite path category; generic functoriality owns reversal of
  composition, while agreement with J-derived symmetry is propositional. The
  canonical dependent PathRecord additionally exposes a nested-Sigma path
  view with stable shaped reflexivity and a reflexive specialized J beta.
*/

require open emdash.emdash3_2;

assert [A : Grpd] ⊢ Obj (Path_cat A) ≡ A;

assert [A : Grpd] (x y : τ A) ⊢
  Hom_cat (Path_cat A) x y ≡ Path_cat (x = y);

assert [A : Grpd] (x : τ A) ⊢
  @id (Path_cat A) x ≡ eq_refl x;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z)) ⊢
  @path_comp_eq_trans A x y p z q
  : τ (
      @comp_fapp0 (Path_cat A) x y z q p
      = @eq_trans A x y z p q);

assert [A : Grpd] (x y : τ A) (p : τ (x = y)) ⊢
  @comp_fapp0 (Path_cat A) x x y p (eq_refl x)
  ≡ p;

assert [A : Grpd] (x y : τ A) ⊢
  Hom_cat (Op_cat (Path_cat A)) x y
  ≡ Path_cat (y = x);

assert [A : Grpd] (x : τ A) ⊢
  @fapp0
    (Op_cat (Path_cat A))
    (Path_cat A)
    (Path_sym_func A)
    x
  ≡ x;

assert [A : Grpd] (x : τ A) ⊢
  @path_sym A x x (eq_refl x)
  ≡ eq_refl x;

assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y))
  [z : τ A]
  (q : τ (y = z)) ⊢
  @comp_fapp0
    (Path_cat A) z y x
    (@path_sym A x y p)
    (@path_sym A y z q)
  ≡ @path_sym A x z
      (@comp_fapp0 (Path_cat A) x y z q p);

assert [A : Grpd]
  [x y : τ A]
  (p : τ (x = y)) ⊢
  @path_sym_agrees_eq_sym A x y p
  : τ (@path_sym A x y p = @eq_sym A x y p);

assert [A : Grpd]
  (r s : τ (PathRecord_grpd A)) ⊢
  @= (PathRecord_grpd A) r s
  ≡ @PathRecordPathView A r s;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @eq_refl (PathRecord_grpd A) r
  ≡ @PathRecordPathRefl A r;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_record_path_tail A r r
    (@PathRecordPathRefl A r)
  ≡ @pathover_refl
      A
      (λ src : τ A, PathRecordTail_grpd src)
      (path_record_src r)
      (path_record_tail r);

assert [A : Grpd]
  (r : τ (PathRecord_grpd A))
  (Q : Π s : τ (PathRecord_grpd A), τ (s = r) → Grpd)
  (u : τ (Q r (@eq_refl (PathRecord_grpd A) r))) ⊢
  @ind_eqr
    (PathRecord_grpd A)
    r Q u r
    (@PathRecordPathRefl A r)
  ≡ u;

assert [A : Grpd]
  (r : τ (PathRecord_grpd A)) ⊢
  @path_sym
    (PathRecord_grpd A)
    r r
    (@PathRecordPathRefl A r)
  ≡ @PathRecordPathRefl A r;
