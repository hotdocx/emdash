/*
  Zero rank as the selected terminal object in the finite-free category.

  Zero-row matrix uniqueness makes every Hom into rank zero contractible.
  The stable arrow observation exposes the existing zero matrix; the generic
  terminal-object owner retains the whole canonical-arrow transfor.
*/

require open emdash.emdash3_2_commutative_algebra_finite_free_binary_products;
require open emdash.emdash3_2_commutative_algebra_matrix_zero_rows;
require open emdash.emdash3_2_terminal_objects;

symbol comm_ring_finite_free_zero_terminal_hom_contr
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : τ (IsContr (Hom (@CommRingFiniteFree_cat R) n zero))
≔ @Struct_sigma
    (@CommRingMatrix R zero n)
    (λ centre : τ (@CommRingMatrix R zero n),
      @Pi_grpd (@CommRingMatrix R zero n)
        (λ f : τ (@CommRingMatrix R zero n),
          @= (@CommRingMatrix R zero n) centre f))
    (@comm_ring_matrix_zero R zero n)
    (λ f : τ (@CommRingMatrix R zero n),
      @eq_sym
        (@CommRingMatrix R zero n)
        f (@comm_ring_matrix_zero R zero n)
        (@comm_ring_matrix_zero_rows_path R n f));

injective symbol comm_ring_finite_free_terminal_zero
  (R : τ CommRing)
  : τ (@TerminalObject (@CommRingFiniteFree_cat R) zero);

injective symbol comm_ring_finite_free_terminal_zero_arrow
  [R : τ CommRing]
  (n : τ Nat_grpd)
  : τ (@CommRingMatrix R zero n);

unif_rule
  @terminal_arrow_fapp0
      _ _ (@comm_ring_finite_free_terminal_zero $R) $n
  ≡ @comm_ring_finite_free_terminal_zero_arrow $R $n
  ↪ [ tt ≡ tt ];

symbol comm_ring_finite_free_terminal_zero_arrow_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R zero n)
      (@terminal_arrow_fapp0
        (@CommRingFiniteFree_cat R) zero
        (@comm_ring_finite_free_terminal_zero R) n)
      (@comm_ring_finite_free_terminal_zero_arrow R n))
≔ @eq_refl _
    (@terminal_arrow_fapp0
      (@CommRingFiniteFree_cat R) zero
      (@comm_ring_finite_free_terminal_zero R) n);

rule @comm_ring_finite_free_terminal_zero_arrow $R $n
  ↪ @comm_ring_matrix_zero $R zero $n;

rule @terminal_hom_contr
      _ _ (@comm_ring_finite_free_terminal_zero $R) $n
  ↪ @comm_ring_finite_free_zero_terminal_hom_contr $R $n;
