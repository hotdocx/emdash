/*
  Library-level path-action refinement for general binary sums.

  The active kernel owns decoded sums, sum_map, and the generic
  PathActionRefinement interface. This one-way module retains the
  former-specific proof-time bases, componentwise eq_ap comparison, and
  selected Sum refinement for library and regression use. No kernel or
  foundational univalence consumer imports it.
*/

require open emdash.emdash3_2;

/*
  Reflexive proof-time basis for componentwise Sum action.

  Generic eq_ap is transparent, while the generic J owner deliberately keeps
  outer Sum reflexivity distinct from component reflexivity. Each stable basis
  therefore has two direct, semantically justified comparisons: one with the
  normalized component action and one with the exact normalized outer-J
  action. The rules do not choose runtime normal forms, and downstream proofs
  compose the two comparisons explicitly rather than relying on experimental
  unification transitivity.
*/
// Stable left reflexive action basis.
injective symbol sum_map_inl_ap_basis
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A)
  (fa : τ A')
  : τ (@= A' fa fa);

// Stable right reflexive action basis.
injective symbol sum_map_inr_ap_basis
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (b : τ B)
  (gb : τ B')
  : τ (@= B' gb gb);

// Proof-time only: the left basis compares with normalized component action.
unif_rule
  @sum_map_inl_ap_basis _ _ $A' _ _ _ _ $fa
  ≡ @eq_refl $A' $fa
  ↪ [ tt ≡ tt ];

// Proof-time only: the left basis compares with normalized outer Sum action.
// The stable basis restricts the transparent ind_eqr pattern to this consumer.
unif_rule
  @sum_map_inl_ap_basis $A $B _ _ _ _ $a _
  ≡ @ind_eqr
      (Sum_grpd $A $B)
      (@sum_inl $A $B $a)
      _
      _
      (@sum_inl $A $B $a)
      (@eq_refl $A $a)
  ↪ [ tt ≡ tt ];

// Proof-time only: the right basis compares with normalized component action.
unif_rule
  @sum_map_inr_ap_basis _ _ _ $B' _ _ _ $gb
  ≡ @eq_refl $B' $gb
  ↪ [ tt ≡ tt ];

// Proof-time only: the right basis compares with normalized outer Sum action.
unif_rule
  @sum_map_inr_ap_basis $A $B _ _ _ _ $b _
  ≡ @ind_eqr
      (Sum_grpd $A $B)
      (@sum_inr $A $B $b)
      _
      _
      (@sum_inr $A $B $b)
      (@eq_refl $B $b)
  ↪ [ tt ≡ tt ];

// Component generic action reaches the stable left basis.
symbol sum_map_inl_component_basis
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A)
  : τ (@=
      (@= A' (f a) (f a))
      (@eq_ap A A' f a a (@eq_refl A a))
      (@sum_map_inl_ap_basis A B A' B' f g a (f a)))
≔ @eq_refl
    (@= A' (f a) (f a))
    (@sum_map_inl_ap_basis A B A' B' f g a (f a));

// The stable left basis reaches outer Sum generic action.
symbol sum_map_inl_basis_outer
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (a : τ A)
  : τ (@=
      (@= A' (f a) (f a))
      (@sum_map_inl_ap_basis A B A' B' f g a (f a))
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a)
        (@sum_inl A B a)
        (@eq_refl A a)))
≔ @eq_refl
    (@= A' (f a) (f a))
    (@sum_map_inl_ap_basis A B A' B' f g a (f a));

// Component generic action reaches the stable right basis.
symbol sum_map_inr_component_basis
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (b : τ B)
  : τ (@=
      (@= B' (g b) (g b))
      (@eq_ap B B' g b b (@eq_refl B b))
      (@sum_map_inr_ap_basis A B A' B' f g b (g b)))
≔ @eq_refl
    (@= B' (g b) (g b))
    (@sum_map_inr_ap_basis A B A' B' f g b (g b));

// The stable right basis reaches outer Sum generic action.
symbol sum_map_inr_basis_outer
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (b : τ B)
  : τ (@=
      (@= B' (g b) (g b))
      (@sum_map_inr_ap_basis A B A' B' f g b (g b))
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inr A B b)
        (@sum_inr A B b)
        (@eq_refl B b)))
≔ @eq_refl
    (@= B' (g b) (g b))
    (@sum_map_inr_ap_basis A B A' B' f g b (g b));

// Left-component paths agree with generic action of the canonical Sum map.
symbol sum_map_inl_eq_ap
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  [a0 a1 : τ A]
  (p : τ (@= A a0 a1))
  : τ (@=
      (@= A' (f a0) (f a1))
      (@eq_ap A A' f a0 a1 p)
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a0)
        (@sum_inl A B a1)
        p))
≔ @ind_eqr A a1
    (λ a0 : τ A, λ p : τ (@= A a0 a1),
      @=
        (@= A' (f a0) (f a1))
        (@eq_ap A A' f a0 a1 p)
        (@eq_ap
          (Sum_grpd A B)
          (Sum_grpd A' B')
          (@sum_map A B A' B' f g)
          (@sum_inl A B a0)
          (@sum_inl A B a1)
          p))
    (@eq_trans
      (@= A' (f a1) (f a1))
      (@eq_ap A A' f a1 a1 (@eq_refl A a1))
      (@sum_map_inl_ap_basis A B A' B' f g a1 (f a1))
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inl A B a1)
        (@sum_inl A B a1)
        (@eq_refl A a1))
      (@sum_map_inl_component_basis A B A' B' f g a1)
      (@sum_map_inl_basis_outer A B A' B' f g a1))
    a0
    p;

// Right-component paths agree with generic action of the canonical Sum map.
symbol sum_map_inr_eq_ap
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  [b0 b1 : τ B]
  (p : τ (@= B b0 b1))
  : τ (@=
      (@= B' (g b0) (g b1))
      (@eq_ap B B' g b0 b1 p)
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inr A B b0)
        (@sum_inr A B b1)
        p))
≔ @ind_eqr B b1
    (λ b0 : τ B, λ p : τ (@= B b0 b1),
      @=
        (@= B' (g b0) (g b1))
        (@eq_ap B B' g b0 b1 p)
        (@eq_ap
          (Sum_grpd A B)
          (Sum_grpd A' B')
          (@sum_map A B A' B' f g)
          (@sum_inr A B b0)
          (@sum_inr A B b1)
          p))
    (@eq_trans
      (@= B' (g b1) (g b1))
      (@eq_ap B B' g b1 b1 (@eq_refl B b1))
      (@sum_map_inr_ap_basis A B A' B' f g b1 (g b1))
      (@eq_ap
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g)
        (@sum_inr A B b1)
        (@sum_inr A B b1)
        (@eq_refl B b1))
      (@sum_map_inr_component_basis A B A' B' f g b1)
      (@sum_map_inr_basis_outer A B A' B' f g b1))
    b0
    p;
/*
  Componentwise selected refinement of a binary-sum map.

  Equal tags delegate to the selected action on the corresponding summand.
  Mixed tags return or eliminate the already-impossible Empty witness. The
  refinement targets the capped canonical path-map action; its proof uses the
  Sum-owned eq_ap comparisons above because that canonical action reduces to
  eq_ap. The selection remains a distinct runtime presentation at open
  endpoints.
*/
// Componentwise selected action map for `sum_map(f,g)`.
symbol sum_path_action_map
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  : τ (@PathActionRefinementMap
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g))
≔ λ x : τ (Sum_grpd A B),
    λ y : τ (Sum_grpd A B),
    λ p : τ (@= (Sum_grpd A B) x y),
      @sum_elim A B
        (λ x0 : τ (Sum_grpd A B),
          @Pi_grpd (Sum_grpd A B)
            (λ y0 : τ (Sum_grpd A B),
              @Pi_grpd (@= (Sum_grpd A B) x0 y0)
                (λ _ : τ (@= (Sum_grpd A B) x0 y0),
                  @= (Sum_grpd A' B')
                    (@sum_map A B A' B' f g x0)
                    (@sum_map A B A' B' f g y0))))
        (λ a0 : τ A,
          @sum_elim A B
            (λ y0 : τ (Sum_grpd A B),
              @Pi_grpd
                (@= (Sum_grpd A B) (@sum_inl A B a0) y0)
                (λ _ : τ (@= (Sum_grpd A B) (@sum_inl A B a0) y0),
                  @= (Sum_grpd A' B')
                    (@sum_map A B A' B' f g (@sum_inl A B a0))
                    (@sum_map A B A' B' f g y0)))
            (λ a1 : τ A,
              λ p0 : τ (@= A a0 a1),
                @path_action_refinement_apply A A' f u a0 a1 p0)
            (λ b1 : τ B,
              λ p0 : τ Empty_grpd, p0))
        (λ b0 : τ B,
          @sum_elim A B
            (λ y0 : τ (Sum_grpd A B),
              @Pi_grpd
                (@= (Sum_grpd A B) (@sum_inr A B b0) y0)
                (λ _ : τ (@= (Sum_grpd A B) (@sum_inr A B b0) y0),
                  @= (Sum_grpd A' B')
                    (@sum_map A B A' B' f g (@sum_inr A B b0))
                    (@sum_map A B A' B' f g y0)))
            (λ a1 : τ A,
              λ p0 : τ Empty_grpd, p0)
            (λ b1 : τ B,
              λ p0 : τ (@= B b0 b1),
                @path_action_refinement_apply B B' g v b0 b1 p0))
        x
        y
        p;

// Pointwise classifier for selected-versus-canonical Sum action agreement.
symbol SumPathActionRefinementCoherenceAt
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  (x y : τ (Sum_grpd A B))
  (p : τ (@= (Sum_grpd A B) x y))
  : Grpd
≔ @=
    (@= (Sum_grpd A' B')
      (@sum_map A B A' B' f g x)
      (@sum_map A B A' B' f g y))
    (@sum_path_action_map A B A' B' f g u v x y p)
    (@fapp1_fapp0
      (Path_cat (Sum_grpd A B))
      (Path_cat (Sum_grpd A' B'))
      (@path_map_func
        (Sum_grpd A B)
        (Sum_grpd A' B')
        (@sum_map A B A' B' f g))
      x y p);

// Componentwise selection agrees with canonical path-map action.
symbol sum_path_action_coherence
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  : τ (@PathActionRefinementCoherence
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g)
      (@sum_path_action_map A B A' B' f g u v))
≔ λ x : τ (Sum_grpd A B),
    λ y : τ (Sum_grpd A B),
    λ p : τ (@= (Sum_grpd A B) x y),
      @sum_elim A B
        (λ x0 : τ (Sum_grpd A B),
          @Pi_grpd (Sum_grpd A B)
            (λ y0 : τ (Sum_grpd A B),
              @Pi_grpd (@= (Sum_grpd A B) x0 y0)
                (λ p0 : τ (@= (Sum_grpd A B) x0 y0),
                  @SumPathActionRefinementCoherenceAt
                    A B A' B' f g u v x0 y0 p0)))
        (λ a0 : τ A,
          @sum_elim A B
            (λ y0 : τ (Sum_grpd A B),
              @Pi_grpd
                (@= (Sum_grpd A B) (@sum_inl A B a0) y0)
                (λ p0 : τ (@= (Sum_grpd A B) (@sum_inl A B a0) y0),
                  @SumPathActionRefinementCoherenceAt
                    A B A' B' f g u v (@sum_inl A B a0) y0 p0))
            (λ a1 : τ A,
              λ p0 : τ (@= A a0 a1),
                @eq_trans
                  (@= A' (f a0) (f a1))
                  (@path_action_refinement_apply A A' f u a0 a1 p0)
                  (@eq_ap A A' f a0 a1 p0)
                  (@eq_ap
                    (Sum_grpd A B)
                    (Sum_grpd A' B')
                    (@sum_map A B A' B' f g)
                    (@sum_inl A B a0)
                    (@sum_inl A B a1)
                    p0)
                  (@path_action_refinement_agrees A A' f u a0 a1 p0)
                  (@sum_map_inl_eq_ap A B A' B' f g a0 a1 p0))
            (λ b1 : τ B,
              λ p0 : τ Empty_grpd,
                @empty_elim
                  (λ q : τ Empty_grpd,
                    @SumPathActionRefinementCoherenceAt
                      A B A' B' f g u v
                      (@sum_inl A B a0)
                      (@sum_inr A B b1)
                      q)
                  p0))
        (λ b0 : τ B,
          @sum_elim A B
            (λ y0 : τ (Sum_grpd A B),
              @Pi_grpd
                (@= (Sum_grpd A B) (@sum_inr A B b0) y0)
                (λ p0 : τ (@= (Sum_grpd A B) (@sum_inr A B b0) y0),
                  @SumPathActionRefinementCoherenceAt
                    A B A' B' f g u v (@sum_inr A B b0) y0 p0))
            (λ a1 : τ A,
              λ p0 : τ Empty_grpd,
                @empty_elim
                  (λ q : τ Empty_grpd,
                    @SumPathActionRefinementCoherenceAt
                      A B A' B' f g u v
                      (@sum_inr A B b0)
                      (@sum_inl A B a1)
                      q)
                  p0)
            (λ b1 : τ B,
              λ p0 : τ (@= B b0 b1),
                @eq_trans
                  (@= B' (g b0) (g b1))
                  (@path_action_refinement_apply B B' g v b0 b1 p0)
                  (@eq_ap B B' g b0 b1 p0)
                  (@eq_ap
                    (Sum_grpd A B)
                    (Sum_grpd A' B')
                    (@sum_map A B A' B' f g)
                    (@sum_inr A B b0)
                    (@sum_inr A B b1)
                    p0)
                  (@path_action_refinement_agrees B B' g v b0 b1 p0)
                  (@sum_map_inr_eq_ap A B A' B' f g b0 b1 p0)))
        x
        y
        p;

// Optional componentwise refinement for the canonical binary-sum map.
symbol sum_path_action_refinement
  [A B A' B' : Grpd]
  (f : τ A → τ A')
  (g : τ B → τ B')
  (u : τ (@PathActionRefinement A A' f))
  (v : τ (@PathActionRefinement B B' g))
  : τ (@PathActionRefinement
      (Sum_grpd A B)
      (Sum_grpd A' B')
      (@sum_map A B A' B' f g))
≔ @path_action_refinement_intro
    (Sum_grpd A B)
    (Sum_grpd A' B')
    (@sum_map A B A' B' f g)
    (@sum_path_action_map A B A' B' f g u v)
    (@sum_path_action_coherence A B A' B' f g u v);
