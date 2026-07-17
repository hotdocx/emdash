/*
  Reviewer milestone: registered successor action for recursive Nat equality.

  Successor equality exposes the predecessor path, so the selected action can
  compute as p |-> p. A stable proof-time basis compares independently with
  component and outer reflexivity, allowing generic J to prove agreement with
  semantic eq_ap without selecting a runtime proof normal form. No unification
  transitivity, successor-specific J beta, or Nat canonicity is assumed.
*/

require open emdash.emdash3_2;

assert [m n : τ Nat_grpd] ⊢
  @= Nat_grpd (succ m) (succ n)
  ≡ @= Nat_grpd m n;

assert (n : τ Nat_grpd) ⊢
  @nat_succ_ap_basis n
  : τ (@= Nat_grpd (succ n) (succ n));

// Typed eq_refl exercises both direct proof-time comparisons.
assert (n : τ Nat_grpd) ⊢
  @eq_refl
    (@= Nat_grpd (succ n) (succ n))
    (@nat_succ_ap_basis n)
  : τ (@=
      (@= Nat_grpd (succ n) (succ n))
      (@nat_succ_ap_basis n)
      (@eq_refl Nat_grpd n));

assert (n : τ Nat_grpd) ⊢
  @eq_refl
    (@= Nat_grpd (succ n) (succ n))
    (@nat_succ_ap_basis n)
  : τ (@=
      (@= Nat_grpd (succ n) (succ n))
      (@nat_succ_ap_basis n)
      (@eq_refl Nat_grpd (succ n)));

assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  @nat_succ_eq_ap m n p
  : τ (@=
      (@= Nat_grpd (succ m) (succ n))
      p
      (@eq_ap
        Nat_grpd Nat_grpd
        (λ k : τ Nat_grpd, succ k)
        m n p));

assert ⊢
  nat_succ_obs_action
  : τ (@ObsAction
      Nat_grpd Nat_grpd
      (λ n : τ Nat_grpd, succ n));

assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  (λ q : τ (@= Nat_grpd (succ m) (succ n)), q)
    (nat_succ_obs_action_map m n p)
  ≡
  (λ q : τ (@= Nat_grpd (succ m) (succ n)), q) p;

assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  (λ q : τ (@= Nat_grpd (succ m) (succ n)), q)
    (@obs_action_apply
      Nat_grpd Nat_grpd
      (λ k : τ Nat_grpd, succ k)
      nat_succ_obs_action
      m n p)
  ≡
  (λ q : τ (@= Nat_grpd (succ m) (succ n)), q) p;

assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  @obs_action_agrees
    Nat_grpd Nat_grpd
    (λ k : τ Nat_grpd, succ k)
    nat_succ_obs_action
    m n p
  : τ (@=
      (@= Nat_grpd (succ m) (succ n))
      p
      (@eq_ap
        Nat_grpd Nat_grpd
        (λ k : τ Nat_grpd, succ k)
        m n p));

assert (n : τ Nat_grpd) ⊢
  @obs_action_agrees
    Nat_grpd Nat_grpd
    (λ k : τ Nat_grpd, succ k)
    nat_succ_obs_action
    n n
    (@eq_refl Nat_grpd n)
  : τ (@=
      (@= Nat_grpd (succ n) (succ n))
      (@eq_refl Nat_grpd n)
      (@eq_refl Nat_grpd (succ n)));

assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  (λ q : τ (@= Nat_grpd (succ (succ m)) (succ (succ n))), q)
    (@obs_action_apply
      Nat_grpd Nat_grpd
      (λ k : τ Nat_grpd, succ (succ k))
      (@obs_action_comp
        Nat_grpd Nat_grpd Nat_grpd
        (λ k : τ Nat_grpd, succ k)
        (λ k : τ Nat_grpd, succ k)
        nat_succ_obs_action
        nat_succ_obs_action)
      m n p)
  ≡
  (λ q : τ (@= Nat_grpd (succ (succ m)) (succ (succ n))), q) p;

// Proof-time comparison does not select either runtime proof normal form.
assertnot (n : τ Nat_grpd) ⊢
  (λ q : τ (@= Nat_grpd (succ n) (succ n)), q)
    (@nat_succ_ap_basis n)
  ≡
  (λ q : τ (@= Nat_grpd (succ n) (succ n)), q)
    (@eq_refl Nat_grpd n);

assertnot (n : τ Nat_grpd) ⊢
  (λ q : τ (@= Nat_grpd (succ n) (succ n)), q)
    (@nat_succ_ap_basis n)
  ≡
  (λ q : τ (@= Nat_grpd (succ n) (succ n)), q)
    (@eq_refl Nat_grpd (succ n));

// Experimental unification transitivity is not assumed.
assertnot (n : τ Nat_grpd) ⊢
  @eq_refl
    (@= Nat_grpd (succ n) (succ n))
    (@eq_refl Nat_grpd n)
  : τ (@=
      (@= Nat_grpd (succ n) (succ n))
      (@eq_refl Nat_grpd n)
      (@eq_refl Nat_grpd (succ n)));

assertnot [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  nat_succ_obs_action_map m n p
  ≡ @eq_ap
      Nat_grpd Nat_grpd
      (λ k : τ Nat_grpd, succ k)
      m n p;

assertnot ⊢
  nat_succ_obs_action
  ≡ @obs_action_from_function
      Nat_grpd Nat_grpd
      (λ k : τ Nat_grpd, succ k);

// The former-specific induction facade accepts arbitrary successor-path motives.
assert [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n)))
  [m : τ Nat_grpd]
  (p : τ (@= Nat_grpd (succ m) (succ n))) ⊢
  @nat_succ_ind_eqr n P u m p
  : τ (P m p);

assert [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n)))
  [m : τ Nat_grpd]
  (p : τ (@= Nat_grpd (succ m) (succ n))) ⊢
  @nat_succ_ind_eqr n P u m p
  ≡ @ind_eqr
      Nat_grpd
      n
      (λ k : τ Nat_grpd, λ q : τ (@= Nat_grpd k n), P k q)
      u
      m
      p;

assert [n : τ Nat_grpd]
  (P : Π m : τ Nat_grpd,
    τ (@= Nat_grpd (succ m) (succ n)) → Grpd)
  (u : τ (P n (@eq_refl Nat_grpd n))) ⊢
  @nat_succ_ind_eqr
    n P u n (@eq_refl Nat_grpd n)
  ≡ u;

// Registered action is a concrete input to the facade.
assert [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    m
    (@obs_action_apply
      Nat_grpd Nat_grpd
      (λ k : τ Nat_grpd, succ k)
      nat_succ_obs_action
      m n p)
  : τ Unit_grpd;

assert (n : τ Nat_grpd) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    n
    (@obs_action_apply
      Nat_grpd Nat_grpd
      (λ k : τ Nat_grpd, succ k)
      nat_succ_obs_action
      n n (@eq_refl Nat_grpd n))
  ≡ tt;

assert (n : τ Nat_grpd) ⊢
  @nat_succ_ind_eqr
    (succ n)
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ (succ n))), Unit_grpd)
    tt
    (succ n)
    (@eq_refl Nat_grpd (succ n))
  ≡ tt;

// The facade adds only component-reflexivity computation.
assertnot (n : τ Nat_grpd) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    n
    (@eq_refl Nat_grpd (succ n))
  ≡ tt;

assertnot (n : τ Nat_grpd) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    n
    (@nat_succ_ap_basis n)
  ≡ tt;

assertnot (n : τ Nat_grpd) ⊢
  @ind_eqr
    Nat_grpd
    (succ n)
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd k (succ n)), Unit_grpd)
    tt
    (succ n)
    (@eq_refl Nat_grpd n)
  ≡ tt;

assertnot [m n : τ Nat_grpd]
  (p : τ (@= Nat_grpd m n)) ⊢
  @nat_succ_ind_eqr
    n
    (λ k : τ Nat_grpd,
      λ _ : τ (@= Nat_grpd (succ k) (succ n)), Unit_grpd)
    tt
    m
    p
  ≡ tt;
