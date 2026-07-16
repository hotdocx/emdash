/*
  Reviewer milestone: recursive visible-constructor Nat equality.

  Zero/successor pairs expose Unit, Empty, or predecessor equality. Generic
  outer reflexivity retains its proof provenance, and the category/endpoint-
  guarded J beta cannot consume foreign or predecessor reflexivity merely
  because the decoded classifier agrees. These checks do not claim Nat
  canonicity, induction-derived no-confusion, or arbitrary structural action.
*/

require open emdash.emdash3_2;

assert ⊢ @= Nat_grpd zero zero ≡ Unit_grpd;

assert (n : τ Nat_grpd) ⊢
  @= Nat_grpd zero (succ n)
  ≡ Empty_grpd;

assert (n : τ Nat_grpd) ⊢
  @= Nat_grpd (succ n) zero
  ≡ Empty_grpd;

assert (n m : τ Nat_grpd) ⊢
  @= Nat_grpd (succ n) (succ m)
  ≡ @= Nat_grpd n m;

assert (n m : τ Nat_grpd) ⊢
  @= Nat_grpd (succ (succ n)) (succ (succ m))
  ≡ @= Nat_grpd n m;

assert ⊢ @eq_refl Nat_grpd zero : τ Unit_grpd;

assert (n : τ Nat_grpd) ⊢
  @eq_refl Nat_grpd (succ n)
  : τ (@= Nat_grpd n n);

assert (n : τ Nat_grpd)
  (P : Π m : τ Nat_grpd, τ (@= Nat_grpd m (succ n)) → Grpd)
  (u : τ (P (succ n) (@eq_refl Nat_grpd (succ n)))) ⊢
  @ind_eqr
    Nat_grpd (succ n) P u (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ u;

assert (n : τ Nat_grpd) ⊢
  @path_sym Nat_grpd
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @eq_refl Nat_grpd (succ n);

assert ⊢
  @path_to_hom
    (Path_cat Nat_grpd) zero zero (@eq_refl Nat_grpd zero)
  ≡ @id (Path_cat Nat_grpd) zero;

assert (n : τ Nat_grpd) ⊢
  @idtoequiv_cat
    (Path_cat Nat_grpd)
    (succ n) (succ n) (@eq_refl Nat_grpd (succ n))
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) (succ n);

// Local runtime, proof-time, and open-endpoint controls only.
assertnot ⊢ @eq_refl Nat_grpd zero ≡ tt;

assertnot (n : τ Nat_grpd) ⊢
  @eq_refl
    (@= Nat_grpd n n)
    (@eq_refl Nat_grpd (succ n))
  : τ (@=
      (@= Nat_grpd n n)
      (@eq_refl Nat_grpd (succ n))
      (@eq_refl Nat_grpd n));

assertnot (n : τ Nat_grpd) ⊢
  @ind_eqr
    Nat_grpd (succ n)
    (λ m : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd m (succ n)), Unit_grpd)
    tt (succ n) (@eq_refl Nat_grpd n)
  ≡ tt;

assertnot ⊢
  @ind_eqr
    Nat_grpd zero
    (λ n : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd n zero), Unit_grpd)
    tt zero (@eq_refl Unit_grpd tt)
  ≡ tt;

assertnot (n : τ Nat_grpd) ⊢
  (λ p : τ (@= Nat_grpd (succ n) (succ n)), p)
    (@path_sym Nat_grpd (succ n) (succ n) (@eq_refl Nat_grpd n))
  ≡
  (λ p : τ (@= Nat_grpd (succ n) (succ n)), p)
    (@eq_refl Nat_grpd n);

assertnot (n : τ Nat_grpd) ⊢
  @idtoequiv_cat
    (Path_cat Nat_grpd) (succ n) (succ n) (@eq_refl Nat_grpd n)
  ≡ @omega_equiv_refl (Path_cat Nat_grpd) (succ n);

assertnot (n : τ Nat_grpd) ⊢
  @= Nat_grpd n n
  ≡ Unit_grpd;

assertnot (n : τ Nat_grpd) ⊢
  @eq_refl Nat_grpd n
  : τ Unit_grpd;
