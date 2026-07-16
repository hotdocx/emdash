/*
  Reviewer milestone: a decoded general binary sum has native left/right
  introductions and dependent elimination with both constructor betas.

  These checks do not claim observational sum identity, a no-confusion or
  canonicity theorem, higher action, or a categorical coproduct property.
*/

flag "eta_equality" on;
flag "print_implicits" on;
flag "print_contexts" on;
flag "print_domains" on;
flag "print_meta_args" on;

require open emdash.emdash3_2;

assert [A B : Grpd] ⊢
  τ (Sum_grpd A B)
  ≡ SumData A B;

assert [A B : Grpd]
  (a : τ A) ⊢
  @sum_inl A B a
  : τ (Sum_grpd A B);

assert [A B : Grpd]
  (b : τ B) ⊢
  @sum_inr A B b
  : τ (Sum_grpd A B);

assert [A B : Grpd]
  (P : τ (Sum_grpd A B) → Grpd)
  (u_inl : Π a : τ A, τ (P (@sum_inl A B a)))
  (u_inr : Π b : τ B, τ (P (@sum_inr A B b)))
  (s : τ (Sum_grpd A B)) ⊢
  @sum_elim A B P u_inl u_inr s
  : τ (P s);

assert [A B : Grpd]
  (P : τ (Sum_grpd A B) → Grpd)
  (u_inl : Π a : τ A, τ (P (@sum_inl A B a)))
  (u_inr : Π b : τ B, τ (P (@sum_inr A B b)))
  (a : τ A) ⊢
  @sum_elim A B P u_inl u_inr (@sum_inl A B a)
  ≡ u_inl a;

assert [A B : Grpd]
  (P : τ (Sum_grpd A B) → Grpd)
  (u_inl : Π a : τ A, τ (P (@sum_inl A B a)))
  (u_inr : Π b : τ B, τ (P (@sum_inr A B b)))
  (b : τ B) ⊢
  @sum_elim A B P u_inl u_inr (@sum_inr A B b)
  ≡ u_inr b;

// A nondependent consumer swaps the two summands through the same eliminator.
assert [A B : Grpd]
  (a : τ A) ⊢
  @sum_elim A B
    (λ _ : τ (Sum_grpd A B), Sum_grpd B A)
    (λ x : τ A, @sum_inr B A x)
    (λ y : τ B, @sum_inl B A y)
    (@sum_inl A B a)
  ≡ @sum_inr B A a;

assert [A B : Grpd]
  (b : τ B) ⊢
  @sum_elim A B
    (λ _ : τ (Sum_grpd A B), Sum_grpd B A)
    (λ x : τ A, @sum_inr B A x)
    (λ y : τ B, @sum_inl B A y)
    (@sum_inr A B b)
  ≡ @sum_inl B A b;

// Conversion controls only: they are not no-confusion or normalization proofs.
assertnot [A B : Grpd]
  (a : τ A)
  (b : τ B) ⊢
  @sum_inl A B a
  ≡ @sum_inr A B b;

assertnot [A B : Grpd]
  (s : τ (Sum_grpd A B)) ⊢
  s
  ≡ @sum_elim A B
      (λ _ : τ (Sum_grpd A B), Sum_grpd A B)
      (λ a : τ A, @sum_inl A B a)
      (λ b : τ B, @sum_inr A B b)
      s;
