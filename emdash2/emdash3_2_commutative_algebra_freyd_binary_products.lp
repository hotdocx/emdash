/*
  Selected computational binary products in the formal Freyd category.

  The product functor is the already-constructed quotient direct-sum functor.
  This module only selects the primitive BinaryProducts witness and connects
  its stable point observations to the constructed quotient operations. The
  generic triangular module retains the whole transfors, higher action, and
  Došen normalization laws.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_direct_sums;
require open emdash.emdash3_2_triangular_binary_products;

// Selected product witness for the formal Freyd category.
injective symbol comm_ring_freyd_binary_products
  (R : τ CommRing)
  : τ (@BinaryProducts
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R));

// Rigid concrete point observations keep the generic triangular heads out of
// the runtime decision tree while exposing their constructed semantics.
injective symbol comm_ring_freyd_binary_proj1
  [R : τ CommRing]
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) P);

injective symbol comm_ring_freyd_binary_proj2
  [R : τ CommRing]
  (P Q : τ (@CommRingPresentation R))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) Q);

injective symbol comm_ring_freyd_binary_pair
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R X P))
  (g : τ (@CommRingFreydHomSet R X Q))
  : τ (@CommRingFreydHomSet R X
      (@comm_ring_presentation_direct_sum R P Q));

unif_rule
  @binary_products_proj1_fapp0
      _ _ (@comm_ring_freyd_binary_products $R) $P $Q
  ≡ @comm_ring_freyd_binary_proj1 $R $P $Q
  ↪ [ tt ≡ tt ];

unif_rule
  @binary_products_proj2_fapp0
      _ _ (@comm_ring_freyd_binary_products $R) $P $Q
  ≡ @comm_ring_freyd_binary_proj2 $R $P $Q
  ↪ [ tt ≡ tt ];

unif_rule
  @binary_products_pair_fapp0
      _ _ (@comm_ring_freyd_binary_products $R)
      $X $P $Q $f $g
  ≡ @comm_ring_freyd_binary_pair $R $X $P $Q $f $g
  ↪ [ tt ≡ tt ];

symbol comm_ring_freyd_binary_proj1_path
  [R : τ CommRing]
  (P Q : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) P)
      (@binary_products_proj1_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_freyd_binary_products R) P Q)
      (@comm_ring_freyd_binary_proj1 R P Q))
≔ @eq_refl _
    (@binary_products_proj1_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) P Q);

symbol comm_ring_freyd_binary_proj2_path
  [R : τ CommRing]
  (P Q : τ (@CommRingPresentation R))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) Q)
      (@binary_products_proj2_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_freyd_binary_products R) P Q)
      (@comm_ring_freyd_binary_proj2 R P Q))
≔ @eq_refl _
    (@binary_products_proj2_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) P Q);

symbol comm_ring_freyd_binary_pair_path
  [R : τ CommRing]
  [X P Q : τ (@CommRingPresentation R)]
  (f : τ (@CommRingFreydHomSet R X P))
  (g : τ (@CommRingFreydHomSet R X Q))
  : τ (@= (@CommRingFreydHomSet R X
      (@comm_ring_presentation_direct_sum R P Q))
      (@binary_products_pair_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_freyd_binary_products R) X P Q f g)
      (@comm_ring_freyd_binary_pair R X P Q f g))
≔ @eq_refl _
    (@binary_products_pair_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) X P Q f g);

rule @comm_ring_freyd_binary_proj1 $R $P $Q
  ↪ @comm_ring_freyd_proj1_class $R $P $Q;

rule @comm_ring_freyd_binary_proj2 $R $P $Q
  ↪ @comm_ring_freyd_proj2_class $R $P $Q;

rule @comm_ring_freyd_binary_pair $R $X $P $Q $f $g
  ↪ @comm_ring_freyd_pair $R $X $P $Q $f $g;
