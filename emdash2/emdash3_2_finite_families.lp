/*
  Nat-indexed finite homogeneous families.

  This one-way standard-library module represents a length-n family as a
  right-associated constant-family Sigma ending in Unit. It derives formation,
  constructors, observations, pointwise map, and sethood from the existing
  Nat/Sigma owners. It introduces no Fin/list/Sum/inductive interface, rewrite
  or unification clause, or package eta.
*/

require open emdash.emdash3_2_nat_arithmetic;

// Length-indexed homogeneous finite tuples: A^0 = 1, A^(n+1) = A x A^n.
symbol FiniteFamily
  (A : Grpd)
  (n : τ Nat_grpd)
  : Grpd
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Grpd_cat)
    Unit_grpd
    (λ _ : τ Nat_grpd, λ tail : Grpd,
      @Σ_ A (λ _ : τ A, tail))
    n;

symbol finite_family_nil
  [A : Grpd]
  : τ (@FiniteFamily A zero)
≔ tt;

symbol finite_family_cons
  [A : Grpd]
  [n : τ Nat_grpd]
  (head : τ A)
  (tail : τ (@FiniteFamily A n))
  : τ (@FiniteFamily A (succ n))
≔ @Struct_sigma A (λ _ : τ A, @FiniteFamily A n) head tail;

symbol finite_family_head
  [A : Grpd]
  [n : τ Nat_grpd]
  (xs : τ (@FiniteFamily A (succ n)))
  : τ A
≔ sigma_Fst xs;

symbol finite_family_tail
  [A : Grpd]
  [n : τ Nat_grpd]
  (xs : τ (@FiniteFamily A (succ n)))
  : τ (@FiniteFamily A n)
≔ sigma_Snd xs;

/*
  Pointwise dependent evidence over a finite family.

  `FiniteFamilyAll(P,n,xs)` is Unit at length zero and the right-associated
  product `P(head(xs)) x All(P,tail(xs))` at a visible successor.  It reuses
  the same Nat-recursive representation as `FiniteFamily`; it is not a new
  list/Fin/inductive interface and introduces no rule or unification clause.
*/
symbol FiniteFamilyAll
  [A : Grpd]
  (P : τ A → Grpd)
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A n))
  : Grpd
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Function_grpd (@FiniteFamily A n0) Grpd_grpd)
    (λ _ : τ (@FiniteFamily A zero), Unit_grpd)
    (λ n0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily A n0)
        Grpd_grpd),
      λ ys : τ (@FiniteFamily A (succ n0)),
        @Product_grpd
          (P (@finite_family_head A n0 ys))
          (rec (@finite_family_tail A n0 ys)))
    n) xs;

symbol finite_family_all_nil
  [A : Grpd]
  [P : τ A → Grpd]
  : τ (@FiniteFamilyAll A P zero (@finite_family_nil A))
≔ tt;

symbol finite_family_all_cons
  [A : Grpd]
  [P : τ A → Grpd]
  [n : τ Nat_grpd]
  [x : τ A]
  [xs : τ (@FiniteFamily A n)]
  (head : τ (P x))
  (tail : τ (@FiniteFamilyAll A P n xs))
  : τ (@FiniteFamilyAll
      A P (succ n) (@finite_family_cons A n x xs))
≔ @Product_pair_grpd
    (P x)
    (@FiniteFamilyAll A P n xs)
    head tail;

symbol finite_family_all_head
  [A : Grpd]
  [P : τ A → Grpd]
  [n : τ Nat_grpd]
  [xs : τ (@FiniteFamily A (succ n))]
  (all : τ (@FiniteFamilyAll A P (succ n) xs))
  : τ (P (@finite_family_head A n xs))
≔ sigma_Fst all;

symbol finite_family_all_tail
  [A : Grpd]
  [P : τ A → Grpd]
  [n : τ Nat_grpd]
  [xs : τ (@FiniteFamily A (succ n))]
  (all : τ (@FiniteFamilyAll A P (succ n) xs))
  : τ (@FiniteFamilyAll
      A P n (@finite_family_tail A n xs))
≔ sigma_Snd all;

symbol finite_family_singleton
  [A : Grpd]
  (x : τ A)
  : τ (@FiniteFamily A (succ zero))
≔ @finite_family_cons A zero x (@finite_family_nil A);

symbol finite_family_pair
  [A : Grpd]
  (x y : τ A)
  : τ (@FiniteFamily A (succ (succ zero)))
≔ @finite_family_cons
    A (succ zero) x (@finite_family_singleton A y);

// Pointwise map, recursively owned by the length index.
symbol finite_family_map
  [A B : Grpd]
  (f : τ (@Function_grpd A B))
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A n))
  : τ (@FiniteFamily B n)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Function_grpd
        (@FiniteFamily A n0)
        (@FiniteFamily B n0))
    (λ _ : τ (@FiniteFamily A zero), @finite_family_nil B)
    (λ n0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@FiniteFamily A n0)
        (@FiniteFamily B n0)),
      λ ys : τ (@FiniteFamily A (succ n0)),
        @finite_family_cons
          B n0
          (f (@finite_family_head A n0 ys))
          (rec (@finite_family_tail A n0 ys)))
    n) xs;

// A finite family of elements of a set remains set-valued.
symbol finite_family_is_set
  (A : Grpd)
  (A_is_set : τ (IsSetGrpd A))
  (n : τ Nat_grpd)
  : τ (IsSetGrpd (@FiniteFamily A n))
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      IsSetGrpd (@FiniteFamily A n0))
    (@prop_is_trunc_succ trunc_minus_one Unit_grpd unit_is_prop)
    (λ n0 : τ Nat_grpd,
      λ tail_is_set : τ (IsSetGrpd (@FiniteFamily A n0)),
        @is_trunc_sigma
          trunc_zero
          A
          (λ _ : τ A, @FiniteFamily A n0)
          A_is_set
          (λ _ : τ A, tail_is_set))
    n;
