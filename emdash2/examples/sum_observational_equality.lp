/*
  Reviewer milestone: visible-constructor general binary-sum equality.

  Equal tags recurse to component equality and distinct tags expose Empty.
  Generic outer reflexivity retains proof provenance, while the guarded J,
  path, and categorical owners do not consume component reflexivity merely
  because it inhabits the reduced classifier. These checks do not claim sum
  canonicity, induction-derived no-confusion, arbitrary action, or categorical
  coproduct structure.
*/

require open emdash.emdash3_2;

assert [A B : Grpd]
  (a0 a1 : τ A) ⊢
  @= (Sum_grpd A B)
    (@sum_inl A B a0) (@sum_inl A B a1)
  ≡ @= A a0 a1;

assert [A B : Grpd]
  (a : τ A)
  (b : τ B) ⊢
  @= (Sum_grpd A B)
    (@sum_inl A B a) (@sum_inr A B b)
  ≡ Empty_grpd;

assert [A B : Grpd]
  (a : τ A)
  (b : τ B) ⊢
  @= (Sum_grpd A B)
    (@sum_inr A B b) (@sum_inl A B a)
  ≡ Empty_grpd;

assert [A B : Grpd]
  (b0 b1 : τ B) ⊢
  @= (Sum_grpd A B)
    (@sum_inr A B b0) (@sum_inr A B b1)
  ≡ @= B b0 b1;

assert [B : Grpd]
  (n m : τ Nat_grpd) ⊢
  @= (Sum_grpd Nat_grpd B)
    (@sum_inl Nat_grpd B (succ n))
    (@sum_inl Nat_grpd B (succ m))
  ≡ @= Nat_grpd n m;

assert [A B : Grpd]
  (a : τ A) ⊢
  @eq_refl (Sum_grpd A B) (@sum_inl A B a)
  : τ (@= A a a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @eq_refl (Sum_grpd A B) (@sum_inr A B b)
  : τ (@= B b b);

assert [A B : Grpd]
  (a : τ A)
  (P : Π s : τ (Sum_grpd A B),
    τ (@= (Sum_grpd A B) s (@sum_inl A B a)) → Grpd)
  (u : τ (P
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a)))) ⊢
  @ind_eqr
    (Sum_grpd A B)
    (@sum_inl A B a)
    P u
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ u;

assert [A B : Grpd]
  (b : τ B) ⊢
  @path_sym
    (Sum_grpd A B)
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ @eq_refl (Sum_grpd A B) (@sum_inr A B b);

assert [A B : Grpd]
  (a : τ A) ⊢
  @path_to_hom
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ @id (Path_cat (Sum_grpd A B)) (@sum_inl A B a);

assert [A B : Grpd]
  (a : τ A) ⊢
  @idtoiso_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inl A B a)
    (@sum_inl A B a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡ @iso_evidence_refl
      (Path_cat (Sum_grpd A B)) (@sum_inl A B a);

assert [A B : Grpd]
  (b : τ B) ⊢
  @idtoequiv_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl (Sum_grpd A B) (@sum_inr A B b))
  ≡ @omega_equiv_refl
      (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

// Local runtime, proof-time, guard, and open-endpoint controls only.
assertnot [A B : Grpd]
  (a : τ A) ⊢
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  ≡
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@eq_refl A a);

assertnot [A B : Grpd]
  (a : τ A) ⊢
  @eq_refl
    (@= A a a)
    (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
  : τ (@=
      (@= A a a)
      (@eq_refl (Sum_grpd A B) (@sum_inl A B a))
      (@eq_refl A a));

assertnot [A B : Grpd]
  (a : τ A) ⊢
  @ind_eqr
    (Sum_grpd A B)
    (@sum_inl A B a)
    (λ s : τ (Sum_grpd A B),
      λ _ : τ (@=
        (Sum_grpd A B) s (@sum_inl A B a)), Unit_grpd)
    tt
    (@sum_inl A B a)
    (@eq_refl A a)
  ≡ tt;

assertnot [A B : Grpd]
  (a : τ A) ⊢
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@path_sym
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)
      (@eq_refl A a))
  ≡
  (λ p : τ (@=
      (Sum_grpd A B)
      (@sum_inl A B a)
      (@sum_inl A B a)), p)
    (@eq_refl A a);

assertnot [A B : Grpd]
  (b : τ B) ⊢
  @path_to_hom
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl B b)
  ≡ @id (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

assertnot [A B : Grpd]
  (b : τ B) ⊢
  @idtoequiv_cat
    (Path_cat (Sum_grpd A B))
    (@sum_inr A B b)
    (@sum_inr A B b)
    (@eq_refl B b)
  ≡ @omega_equiv_refl
      (Path_cat (Sum_grpd A B)) (@sum_inr A B b);

assertnot [A B : Grpd]
  (s : τ (Sum_grpd A B)) ⊢
  @= (Sum_grpd A B) s s
  ≡ Unit_grpd;

assertnot [A B : Grpd]
  (s : τ (Sum_grpd A B)) ⊢
  @eq_refl (Sum_grpd A B) s
  : τ Unit_grpd;
