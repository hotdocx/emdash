/* Reviewer-facing concatenation and splitting of finite families. */

require open emdash.emdash3_2_finite_family_sums;

assert [A : Grpd]
  (n : τ Nat_grpd)
  (ys : τ (@FiniteFamily A n)) ⊢
  @finite_family_append A zero n (@finite_family_nil A) ys
  ≡ ys;

assert [A : Grpd]
  (m n : τ Nat_grpd)
  (x : τ A)
  (xs : τ (@FiniteFamily A m))
  (ys : τ (@FiniteFamily A n)) ⊢
  @finite_family_append A (succ m) n
    (@finite_family_cons A m x xs) ys
  ≡ @finite_family_cons A (@nat_add m n) x
      (@finite_family_append A m n xs ys);

assert [A : Grpd]
  (m n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A m))
  (ys : τ (@FiniteFamily A n)) ⊢
  @finite_family_take_append_path A m n xs ys
  : τ (@= (@FiniteFamily A m)
      (@finite_family_take_left A m n
        (@finite_family_append A m n xs ys))
      xs);

assert [A : Grpd]
  (m n : τ Nat_grpd)
  (zs : τ (@FiniteFamily A (@nat_add m n))) ⊢
  @finite_family_append_split_path A m n zs
  : τ (@= (@FiniteFamily A (@nat_add m n))
      (@finite_family_append A m n
        (@finite_family_take_left A m n zs)
        (@finite_family_drop_left A m n zs))
      zs);

assertnot [A : Grpd]
  (m n : τ Nat_grpd)
  (xs xs' : τ (@FiniteFamily A m))
  (ys : τ (@FiniteFamily A n)) ⊢
  @finite_family_append A m n xs ys
  ≡ @finite_family_append A m n xs' ys;
