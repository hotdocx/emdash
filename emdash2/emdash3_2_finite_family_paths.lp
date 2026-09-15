/* Paths of finite tuples, derived from the existing Sigma path owner. */
require open emdash.emdash3_2_finite_families;

// The ordinary dependent-pair path constructor assembles two tuple paths.
symbol finite_family_cons_path [A : Grpd] [n : τ Nat_grpd]
  [x y : τ A] [xs ys : τ (@FiniteFamily A n)]
  (p : τ (@= A x y)) (q : τ (@= (@FiniteFamily A n) xs ys))
  : τ (@= (@FiniteFamily A (succ n))
    (@finite_family_cons A n x xs) (@finite_family_cons A n y ys))
≔ @sigma_path_intro A (λ _ : τ A, @FiniteFamily A n) x y xs ys p
    (@const_pathover A (@FiniteFamily A n) x y xs ys p q);
