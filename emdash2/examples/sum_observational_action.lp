/*
  Reviewer milestone: componentwise path-action refinement for binary sums.

  A canonical map combines selected refinements on the two summands. Equal
  tags compute componentwise, mixed tags retain the impossible Empty witness,
  and the result agrees propositionally with canonical `path_map_func` action.
  The reflexive eq_ap bridge is proof-time only: runtime proof provenance
  remains visible, and no transitive unification collapse is assumed.
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
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g)) ⊢
  @sum_path_action_refinement A B A' B' f g u v
  : τ (@PathActionRefinement
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1)) ⊢
  (λ q : τ (@= A' (f a0) (f a1)), q)
    (@path_action_refinement_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_path_action_refinement A B A' B' f g u v)
      (@sum_inl A B a0) (@sum_inl A B a1) p)
  ≡
  (λ q : τ (@= A' (f a0) (f a1)), q)
    (@path_action_refinement_apply A A' f u a0 a1 p);

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  [b0 b1 : τ B]
  (p : τ (@= B b0 b1)) ⊢
  (λ q : τ (@= B' (g b0) (g b1)), q)
    (@path_action_refinement_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_path_action_refinement A B A' B' f g u v)
      (@sum_inr A B b0) (@sum_inr A B b1) p)
  ≡
  (λ q : τ (@= B' (g b0) (g b1)), q)
    (@path_action_refinement_apply B B' g v b0 b1 p);

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  (a : τ A)
  (b : τ B)
  (p : τ Empty_grpd) ⊢
  (λ q : τ Empty_grpd, q)
    (@path_action_refinement_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_path_action_refinement A B A' B' f g u v)
      (@sum_inl A B a) (@sum_inr A B b) p)
  ≡ (λ q : τ Empty_grpd, q) p;

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  (a : τ A)
  (b : τ B)
  (p : τ Empty_grpd) ⊢
  (λ q : τ Empty_grpd, q)
    (@path_action_refinement_apply
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_path_action_refinement A B A' B' f g u v)
      (@sum_inr A B b) (@sum_inl A B a) p)
  ≡ (λ q : τ Empty_grpd, q) p;

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1)) ⊢
  @path_action_refinement_agrees
    (Sum_grpd A B)
    (Sum_grpd A' B')
    (@sum_map A B A' B' f g)
    (@sum_path_action_refinement A B A' B' f g u v)
    (@sum_inl A B a0) (@sum_inl A B a1) p
  : τ (@=
      (@= A' (f a0) (f a1))
      (@path_action_refinement_apply A A' f u a0 a1 p)
      (@fapp1_fapp0
        (Path_cat (Sum_grpd A B))
        (Path_cat (Sum_grpd A' B'))
        (@path_map_func
          (Sum_grpd A B)
          (Sum_grpd A' B')
          (@sum_map A B A' B' f g))
        (@sum_inl A B a0)
        (@sum_inl A B a1)
        p));

assert [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  [b0 b1 : τ B]
  (p : τ (@= B b0 b1)) ⊢
  @path_action_refinement_agrees
    (Sum_grpd A B)
    (Sum_grpd A' B')
    (@sum_map A B A' B' f g)
    (@sum_path_action_refinement A B A' B' f g u v)
    (@sum_inr A B b0) (@sum_inr A B b1) p
  : τ (@=
      (@= B' (g b0) (g b1))
      (@path_action_refinement_apply B B' g v b0 b1 p)
      (@fapp1_fapp0
        (Path_cat (Sum_grpd A B))
        (Path_cat (Sum_grpd A' B'))
        (@path_map_func
          (Sum_grpd A B)
          (Sum_grpd A' B')
          (@sum_map A B A' B' f g))
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
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  [x y : τ (Sum_grpd A B)]
  (p : τ (@= (Sum_grpd A B) x y)) ⊢
  @sum_path_action_map A B A' B' f g u v x y p
  ≡ @fapp1_fapp0
      (Path_cat (Sum_grpd A B))
      (Path_cat (Sum_grpd A' B'))
      (@path_map_func
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g))
      x y p;

assertnot [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g)) ⊢
  @sum_path_action_refinement A B A' B' f g u v
  ≡ @path_action_refinement_canonical
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g);
