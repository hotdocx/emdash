/*
  Reusable natural-number arithmetic and sethood prerequisites.

  This one-way library module is independent of the walking-endomorphism
  presentation.  The directed-HIT/BNat module imports it, so users of Nat
  addition or sethood do not acquire the walking-category rules and unifiers.
*/

require open emdash.emdash3_2;

/*
  Natural-number addition.

  The primary recursion is on the left argument.  The open right-unit fold is
  an intentional second equation: it joins the two ordinary category-unit
  orders in one-object monoid presentations.  The two reduction paths at
  `nat_add (succ m) zero` meet at `succ m`.
*/
injective symbol nat_add
  (m n : τ Nat_grpd)
  : τ Nat_grpd;

rule @nat_add zero $n ↪ $n
with @nat_add (succ $m) $n ↪ succ (@nat_add $m $n)
with @nat_add $m zero ↪ $m;

// Associativity of the selected addition orientation, by Nat induction.
symbol nat_add_assoc
  (m n k : τ Nat_grpd)
  : τ (@= Nat_grpd
      (@nat_add (@nat_add m n) k)
      (@nat_add m (@nat_add n k)))
≔ @nat_elim
    (λ m : τ Nat_grpd,
      @= Nat_grpd
        (@nat_add (@nat_add m n) k)
        (@nat_add m (@nat_add n k)))
    (@eq_refl Nat_grpd (@nat_add n k))
    (λ m0 : τ Nat_grpd,
      λ ih : τ (@= Nat_grpd
        (@nat_add (@nat_add m0 n) k)
        (@nat_add m0 (@nat_add n k))),
      ih)
    m;

// Unit is contractible, using its generated dependent eliminator.
symbol unit_is_contr
  : τ (IsContr Unit_grpd)
≔ @Struct_sigma
    Unit_grpd
    (λ centre : τ Unit_grpd,
      @Pi_grpd Unit_grpd
        (λ x : τ Unit_grpd, @= Unit_grpd centre x))
    tt
    (λ x : τ Unit_grpd,
      @ind_unit
        (λ x : τ Unit_grpd, @= Unit_grpd tt x)
        (@eq_refl Unit_grpd tt)
        x);

// Unit is proposition-valued by general contractibility monotonicity.
symbol unit_is_prop
  : τ (IsPropGrpd Unit_grpd)
≔ @is_contr_is_prop Unit_grpd unit_is_contr;

// Empty is proposition-valued by elimination at its first endpoint.
symbol empty_is_prop
  : τ (IsPropGrpd Empty_grpd)
≔ λ x : τ Empty_grpd,
    @empty_elim
      (λ _ : τ Empty_grpd,
        @Pi_grpd Empty_grpd
          (λ y : τ Empty_grpd,
            IsContr (@= Empty_grpd x y)))
      x;

/*
  Nat is set-valued.

  Nested Nat induction reduces every visible equality classifier to Unit or
  Empty and reuses the proposition-valuedness proofs above.  This is an
  internal inhabitant of `IsSetGrpd Nat_grpd`, not a conclusion inferred only
  from constructor no-confusion rewrites.
*/
symbol nat_is_set
  : τ (IsSetGrpd Nat_grpd)
≔ λ m : τ Nat_grpd,
    @nat_elim
      (λ m : τ Nat_grpd,
        @Pi_grpd Nat_grpd
          (λ n : τ Nat_grpd,
            IsPropGrpd (@= Nat_grpd m n)))
      (λ n : τ Nat_grpd,
        @nat_elim
          (λ n : τ Nat_grpd,
            IsPropGrpd (@= Nat_grpd zero n))
          unit_is_prop
          (λ n0 : τ Nat_grpd,
            λ _ : τ (IsPropGrpd (@= Nat_grpd zero n0)),
            empty_is_prop)
          n)
      (λ m0 : τ Nat_grpd,
        λ ih : τ (@Pi_grpd Nat_grpd
          (λ n : τ Nat_grpd,
            IsPropGrpd (@= Nat_grpd m0 n))),
        λ n : τ Nat_grpd,
          @nat_elim
            (λ n : τ Nat_grpd,
              IsPropGrpd (@= Nat_grpd (succ m0) n))
            empty_is_prop
            (λ n0 : τ Nat_grpd,
              λ _ : τ (IsPropGrpd
                (@= Nat_grpd (succ m0) n0)),
              ih n0)
            n)
      m;
