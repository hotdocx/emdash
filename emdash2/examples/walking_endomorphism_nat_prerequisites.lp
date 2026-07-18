/*
  Reviewer milestone: retained arithmetic prerequisites for the walking
  endomorphism plan.

  Addition computes in the selected categorical order, its associativity is
  proved by Nat induction, and Nat carries an internal sethood witness. This
  file intentionally isolates the reusable arithmetic slice. The full
  directed-HIT/BNat milestone is exercised in
  examples/walking_endomorphism_hit.lp.
*/

require open emdash.emdash3_2_nat_arithmetic;

// Addition computes at both constructors and both open unit boundaries.
assert (n : τ Nat_grpd) ⊢
  @nat_add zero n
  ≡ n;

assert (m n : τ Nat_grpd) ⊢
  @nat_add (succ m) n
  ≡ succ (@nat_add m n);

assert (m : τ Nat_grpd) ⊢
  @nat_add m zero
  ≡ m;

assert ⊢
  @nat_add (succ (succ zero)) (succ zero)
  ≡ succ (succ (succ zero));

// Associativity is a transparent induction proof, not a global equation.
assert (m n k : τ Nat_grpd) ⊢
  @nat_add_assoc m n k
  : τ (@= Nat_grpd
      (@nat_add (@nat_add m n) k)
      (@nat_add m (@nat_add n k)));

// The sethood claim is backed by an internal inhabitant.
assert ⊢
  nat_is_set
  : τ (IsSetGrpd Nat_grpd);

assert (m n : τ Nat_grpd) ⊢
  nat_is_set m n
  : τ (IsPropGrpd (@= Nat_grpd m n));

// No commutative runtime normalization was silently installed.
assertnot (m n : τ Nat_grpd) ⊢
  @nat_add m n
  ≡ @nat_add n m;
