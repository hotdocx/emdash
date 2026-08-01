/*
  Nat-indexed finite homogeneous families.

  This one-way standard-library module represents a length-n family as a
  right-associated constant-family Sigma ending in Unit. It derives formation,
  constructors, observations, pointwise map, dependent evidence, dependent
  evidence over an already-selected evidence family, and sethood from the
  existing Nat/Sigma owners. It introduces no Fin/list/Sum/inductive
  interface, rewrite or unification clause, or package eta.
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

/*
  Dependent evidence over already-selected dependent evidence.

  `FiniteFamilyAllOver(P,Q,n,xs,evidence)` is Unit at zero and stores
  `Q(x,px)` for every aligned pair `x`/`px` in `xs`/`evidence`.  Its pointwise
  map below accepts both source and target selections explicitly; it neither
  chooses target evidence nor identifies different choices.
*/
symbol FiniteFamilyAllOver
  [A : Grpd]
  (P : τ A → Grpd)
  (Q : Π x : τ A, τ (P x) → Grpd)
  (n : τ Nat_grpd)
  (xs : τ (@FiniteFamily A n))
  (evidence : τ (@FiniteFamilyAll A P n xs))
  : Grpd
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd
        (@FiniteFamily A n0)
        (λ xs0 : τ (@FiniteFamily A n0),
          @Function_grpd
            (@FiniteFamilyAll A P n0 xs0)
            Grpd_grpd))
    (λ xs0 : τ (@FiniteFamily A zero),
      λ _ : τ (@FiniteFamilyAll A P zero xs0),
        Unit_grpd)
    (λ n0 : τ Nat_grpd,
      λ rec : τ (@Pi_grpd
        (@FiniteFamily A n0)
        (λ xs0 : τ (@FiniteFamily A n0),
          @Function_grpd
            (@FiniteFamilyAll A P n0 xs0)
            Grpd_grpd)),
      λ xs0 : τ (@FiniteFamily A (succ n0)),
      λ evidence0 : τ (@FiniteFamilyAll A P (succ n0) xs0),
        @Product_grpd
          (Q
            (@finite_family_head A n0 xs0)
            (@finite_family_all_head A P n0 xs0 evidence0))
          (rec
            (@finite_family_tail A n0 xs0)
            (@finite_family_all_tail A P n0 xs0 evidence0)))
    n) xs evidence;

symbol finite_family_all_over_nil
  [A : Grpd]
  [P : τ A → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  : τ (@FiniteFamilyAllOver
      A P Q zero
      (@finite_family_nil A)
      (@finite_family_all_nil A P))
≔ tt;

symbol finite_family_all_over_cons
  [A : Grpd]
  [P : τ A → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [n : τ Nat_grpd]
  [x : τ A]
  [xs : τ (@FiniteFamily A n)]
  [px : τ (P x)]
  [evidence : τ (@FiniteFamilyAll A P n xs)]
  (head : τ (Q x px))
  (tail : τ (@FiniteFamilyAllOver
      A P Q n xs evidence))
  : τ (@FiniteFamilyAllOver
      A P Q
      (succ n)
      (@finite_family_cons A n x xs)
      (@finite_family_all_cons A P n x xs px evidence))
≔ @Product_pair_grpd
    (Q x px)
    (@FiniteFamilyAllOver A P Q n xs evidence)
    head tail;

symbol finite_family_all_over_head
  [A : Grpd]
  [P : τ A → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [n : τ Nat_grpd]
  [xs : τ (@FiniteFamily A (succ n))]
  [evidence : τ (@FiniteFamilyAll A P (succ n) xs)]
  (all : τ (@FiniteFamilyAllOver
      A P Q (succ n) xs evidence))
  : τ (Q
      (@finite_family_head A n xs)
      (@finite_family_all_head A P n xs evidence))
≔ sigma_Fst all;

symbol finite_family_all_over_tail
  [A : Grpd]
  [P : τ A → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [n : τ Nat_grpd]
  [xs : τ (@FiniteFamily A (succ n))]
  [evidence : τ (@FiniteFamilyAll A P (succ n) xs)]
  (all : τ (@FiniteFamilyAllOver
      A P Q (succ n) xs evidence))
  : τ (@FiniteFamilyAllOver
      A P Q n
      (@finite_family_tail A n xs)
      (@finite_family_all_tail A P n xs evidence))
≔ sigma_Snd all;

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

// Pointwise transformation over explicit source and target evidence choices.
symbol FiniteFamilyAllOverMap
  [A B : Grpd]
  (map : τ (@Function_grpd A B))
  [P : τ A → Grpd]
  [P2 : τ B → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [Q2 : Π y : τ B, τ (P2 y) → Grpd]
  (n : τ Nat_grpd)
  : Grpd
≔ @Pi_grpd
    (@FiniteFamily A n)
    (λ xs : τ (@FiniteFamily A n),
      @Pi_grpd
        (@FiniteFamilyAll A P n xs)
        (λ source_evidence : τ (@FiniteFamilyAll A P n xs),
          @Pi_grpd
            (@FiniteFamilyAll
              B P2 n (@finite_family_map A B map n xs))
            (λ target_evidence : τ (@FiniteFamilyAll
                B P2 n (@finite_family_map A B map n xs)),
              @Function_grpd
                (@FiniteFamilyAllOver
                  A P Q n xs source_evidence)
                (@FiniteFamilyAllOver
                  B P2 Q2 n
                  (@finite_family_map A B map n xs)
                  target_evidence))));

symbol finite_family_all_over_map
  [A B : Grpd]
  (map : τ (@Function_grpd A B))
  [P : τ A → Grpd]
  [P2 : τ B → Grpd]
  [Q : Π x : τ A, τ (P x) → Grpd]
  [Q2 : Π y : τ B, τ (P2 y) → Grpd]
  (step : Π x : τ A,
    Π px : τ (P x),
    Π py : τ (P2 (map x)),
      τ (Q x px) → τ (Q2 (map x) py))
  (n : τ Nat_grpd)
  : τ (@FiniteFamilyAllOverMap
      A B map P P2 Q Q2 n)
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      @FiniteFamilyAllOverMap
        A B map P P2 Q Q2 n0)
    (λ _ : τ (@FiniteFamily A zero),
      λ _ : τ (@FiniteFamilyAll
        A P zero (@finite_family_nil A)),
      λ _ : τ (@FiniteFamilyAll
        B P2 zero (@finite_family_nil B)),
      λ _ : τ (@FiniteFamilyAllOver
        A P Q zero
        (@finite_family_nil A)
        (@finite_family_all_nil A P)),
        tt)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@FiniteFamilyAllOverMap
        A B map P P2 Q Q2 n0),
      λ xs0 : τ (@FiniteFamily A (succ n0)),
      λ source_evidence0 : τ (@FiniteFamilyAll
          A P (succ n0) xs0),
      λ target_evidence0 : τ (@FiniteFamilyAll
          B P2 (succ n0)
          (@finite_family_map A B map (succ n0) xs0)),
      λ source_over0 : τ (@FiniteFamilyAllOver
          A P Q (succ n0) xs0 source_evidence0),
        @Product_pair_grpd
          (Q2
            (map (@finite_family_head A n0 xs0))
            (@finite_family_all_head
              B P2 n0
              (@finite_family_map A B map (succ n0) xs0)
              target_evidence0))
          (@FiniteFamilyAllOver
            B P2 Q2 n0
            (@finite_family_map
              A B map n0 (@finite_family_tail A n0 xs0))
            (@finite_family_all_tail
              B P2 n0
              (@finite_family_map A B map (succ n0) xs0)
              target_evidence0))
          (step
            (@finite_family_head A n0 xs0)
            (@finite_family_all_head
              A P n0 xs0 source_evidence0)
            (@finite_family_all_head
              B P2 n0
              (@finite_family_map A B map (succ n0) xs0)
              target_evidence0)
            (sigma_Fst source_over0))
          (ih
            (@finite_family_tail A n0 xs0)
            (@finite_family_all_tail
              A P n0 xs0 source_evidence0)
            (@finite_family_all_tail
              B P2 n0
              (@finite_family_map A B map (succ n0) xs0)
              target_evidence0)
            (sigma_Snd source_over0)))
    n;

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
