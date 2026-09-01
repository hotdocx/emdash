/* Reviewer-facing finite-free product, terminal, and additive consumers. */

require open emdash.emdash3_2_commutative_algebra_finite_free_additive;

// Stable product observations expose the canonical matrices.
assert
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  ⊢ @comm_ring_finite_free_binary_proj1 R m n
  ≡ @comm_ring_matrix_proj1 R m n;

assert
  (R : τ CommRing)
  (x m n : τ Nat_grpd)
  (f : τ (@CommRingMatrix R m x))
  (g : τ (@CommRingMatrix R n x))
  ⊢ @comm_ring_finite_free_binary_pair R x m n f g
  ≡ @comm_ring_matrix_vertical R m n x f g;

// Generic triangular beta remains the runtime computation owner.
assert
  (R : τ CommRing)
  (x m n : τ Nat_grpd)
  (f : τ (@CommRingMatrix R m x))
  (g : τ (@CommRingMatrix R n x))
  ⊢ @comp_fapp0
      (@CommRingFiniteFree_cat R)
      x (@nat_add m n) m
      (@binary_products_proj1_fapp0
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        (@comm_ring_finite_free_binary_products R) m n)
      (@binary_products_pair_fapp0
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        (@comm_ring_finite_free_binary_products R) x m n f g)
  ≡ f;

// Terminal observations expose zero-row uniqueness and the selected zero map.
assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  ⊢ @comm_ring_finite_free_terminal_zero_arrow R n
  ≡ @comm_ring_matrix_zero R zero n;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  ⊢ @terminal_hom_contr
      (@CommRingFiniteFree_cat R) zero
      (@comm_ring_finite_free_terminal_zero R) n
  ≡ @comm_ring_finite_free_zero_terminal_hom_contr R n;

// The final additive package reuses the exact preadditive structure.
assert
  (R : τ CommRing)
  ⊢ @additive_preadditive
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero
      (@comm_ring_finite_free_additive R)
  ≡ @comm_ring_finite_free_preadditive R;

// Generic additive injections are available without a second coproduct theory.
assert
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  ⊢ @additive_inj1_fapp0
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero
      (@comm_ring_finite_free_additive R) m n
  : τ (@CommRingMatrix R (@nat_add m n) m);
