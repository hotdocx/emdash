/*
  Reviewer milestone: path categories.

  This demonstrates that equality/path data is internalized as a category:
  objects are points, homs are path categories, identities are reflexivity, and
  composition is path transitivity.
*/

require open emdash.emdash3_2;

assert [A : Grpd] ⊢ Obj (Path_cat A) ≡ A;

assert [A : Grpd] (x y : τ A) ⊢
  Hom_cat (Path_cat A) x y ≡ Path_cat (x = y);

assert [A : Grpd] (x : τ A) ⊢
  @id (Path_cat A) x ≡ eq_refl x;

assert [A : Grpd] (x y z : τ A) (p : τ (x = y)) (q : τ (y = z)) ⊢
  @comp_fapp0 (Path_cat A) x y z q p ≡ eq_trans p q;
