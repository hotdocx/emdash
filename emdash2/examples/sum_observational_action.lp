/*
  Reviewer milestone: componentwise observational action for binary sums.

  A canonical map acts through registered actions on the two summands. Equal
  tags compute componentwise, mixed tags retain the impossible Empty witness,
  and the resulting ObsAction agrees propositionally with generic eq_ap.
  The reflexive bridge is proof-time only: runtime proof provenance remains
  visible, and no transitive unification collapse is assumed.
*/

require open emdash.emdash3_2;
require open emdash.emdash3_2_sum_observational_action;

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A) ⊢
  @sum_map A B A' B' f g (@sum_inl A B a)
  ≡ @sum_inl A' B' (f a);

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (b : τ B) ⊢
  @sum_map A B A' B' f g (@sum_inr A B b)
  ≡ @sum_inr A' B' (g b);

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1)) ⊢
  @sum_map_inl_eq_ap A B A' B' f g a0 a1 p
  : τ (@=
      (@= A' (f a0) (f a1))
      (@eq_ap A A' f a0 a1 p)
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a0)
        (@sum_inl A B a1)
        p));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  [b0 b1 : τ B]
  (p : τ (@= B b0 b1)) ⊢
  @sum_map_inr_eq_ap A B A' B' f g b0 b1 p
  : τ (@=
      (@= B' (g b0) (g b1))
      (@eq_ap B B' g b0 b1 p)
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inr A B b0)
        (@sum_inr A B b1)
        p));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g)) ⊢
  @sum_obs_action A B A' B' f g u v
  : τ (@ObsAction
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1)) ⊢
  (λ q : τ (@= A' (f a0) (f a1)), q)
    (@obs_action_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_obs_action A B A' B' f g u v)
      (@sum_inl A B a0) (@sum_inl A B a1) p)
  ≡
  (λ q : τ (@= A' (f a0) (f a1)), q)
    (@obs_action_apply A A' f u a0 a1 p);

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  [b0 b1 : τ B]
  (p : τ (@= B b0 b1)) ⊢
  (λ q : τ (@= B' (g b0) (g b1)), q)
    (@obs_action_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_obs_action A B A' B' f g u v)
      (@sum_inr A B b0) (@sum_inr A B b1) p)
  ≡
  (λ q : τ (@= B' (g b0) (g b1)), q)
    (@obs_action_apply B B' g v b0 b1 p);

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  (a : τ A)
  (b : τ B)
  (p : τ Empty_grpd) ⊢
  (λ q : τ Empty_grpd, q)
    (@obs_action_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_obs_action A B A' B' f g u v)
      (@sum_inl A B a) (@sum_inr A B b) p)
  ≡ (λ q : τ Empty_grpd, q) p;

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  (a : τ A)
  (b : τ B)
  (p : τ Empty_grpd) ⊢
  (λ q : τ Empty_grpd, q)
    (@obs_action_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_obs_action A B A' B' f g u v)
      (@sum_inr A B b) (@sum_inl A B a) p)
  ≡ (λ q : τ Empty_grpd, q) p;

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1)) ⊢
  @obs_action_agrees
    (Sum_grpd A B)
    (Sum_grpd A' B')
    (@sum_map A B A' B' f g)
    (@sum_obs_action A B A' B' f g u v)
    (@sum_inl A B a0) (@sum_inl A B a1) p
  : τ (@=
      (@= A' (f a0) (f a1))
      (@obs_action_apply A A' f u a0 a1 p)
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a0)
        (@sum_inl A B a1)
        p));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  [b0 b1 : τ B]
  (p : τ (@= B b0 b1)) ⊢
  @obs_action_agrees
    (Sum_grpd A B)
    (Sum_grpd A' B')
    (@sum_map A B A' B' f g)
    (@sum_obs_action A B A' B' f g u v)
    (@sum_inr A B b0) (@sum_inr A B b1) p
  : τ (@=
      (@= B' (g b0) (g b1))
      (@obs_action_apply B B' g v b0 b1 p)
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inr A B b0)
        (@sum_inr A B b1)
        p));

// Typed eq_refl exercises the two direct left-basis comparisons.
assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A) ⊢
  @eq_refl
    (@= A' (f a) (f a))
    (@sum_map_inl_ap_basis A B A' B' f g a (f a))
  : τ (@=
      (@= A' (f a) (f a))
      (@sum_map_inl_ap_basis A B A' B' f g a (f a))
      (@eq_refl A' (f a)));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A) ⊢
  @eq_refl
    (@= A' (f a) (f a))
    (@sum_map_inl_ap_basis A B A' B' f g a (f a))
  : τ (@=
      (@= A' (f a) (f a))
      (@sum_map_inl_ap_basis A B A' B' f g a (f a))
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a)
        (@sum_inl A B a)
        (@eq_refl A a)));

assertnot [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A) ⊢
  (λ q : τ (@= A' (f a) (f a)), q)
    (@sum_map_inl_ap_basis A B A' B' f g a (f a))
  ≡
  (λ q : τ (@= A' (f a) (f a)), q)
    (@eq_refl A' (f a));

assertnot [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A) ⊢
  @eq_refl
    (@= A' (f a) (f a))
    (@eq_ap
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_inl A B a)
      (@sum_inl A B a)
      (@eq_refl A a))
  : τ (@=
      (@= A' (f a) (f a))
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a)
        (@sum_inl A B a)
        (@eq_refl A a))
      (@eq_refl A' (f a)));

assertnot [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g))
  [x y : τ (Sum_grpd A B)]
  (p : τ (@= (Sum_grpd A B) x y)) ⊢
  @sum_obs_action_map A B A' B' f g u v x y p
  ≡ @eq_ap
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      x y p;

assertnot [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@ObsAction A A' f))
  (v : τ (@ObsAction B B' g)) ⊢
  @sum_obs_action A B A' B' f g u v
  ≡ @obs_action_from_function
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g);
