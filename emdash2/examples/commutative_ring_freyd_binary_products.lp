/* Reviewer-facing selected Freyd binary products. */

require open emdash.emdash3_2_commutative_algebra_freyd_binary_products;

assert (R : τ CommRing) ⊢
  @comm_ring_freyd_binary_products R
  : τ (@BinaryProducts
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R));

assert (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingFreydHomSet R X P))
  (g : τ (@CommRingFreydHomSet R X Q)) ⊢
  @comm_ring_freyd_binary_pair_path R X P Q f g
  : τ (@= (@CommRingFreydHomSet R X
      (@comm_ring_presentation_direct_sum R P Q))
      (@binary_products_pair_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_freyd_binary_products R) X P Q f g)
      (@comm_ring_freyd_pair R X P Q f g));

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @comm_ring_freyd_binary_proj1_path R P Q
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) P)
      (@binary_products_proj1_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_freyd_binary_products R) P Q)
      (@comm_ring_freyd_proj1_class R P Q));

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @comm_ring_freyd_binary_proj2_path R P Q
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_presentation_direct_sum R P Q) Q)
      (@binary_products_proj2_fapp0
        (@CommRingFreydPresentation_cat R)
        (@comm_ring_freyd_direct_sum_func R)
        (@comm_ring_freyd_binary_products R) P Q)
      (@comm_ring_freyd_proj2_class R P Q));

assert (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R))
  (f : τ (@CommRingFreydHomSet R X P))
  (g : τ (@CommRingFreydHomSet R X Q)) ⊢
  @comp_fapp0
    (@CommRingFreydPresentation_cat R)
    X (@comm_ring_presentation_direct_sum R P Q) P
    (@binary_products_proj1_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) P Q)
    (@binary_products_pair_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) X P Q f g)
  ≡ f;

assert (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @binary_products_pair_fapp0
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_freyd_binary_products R)
    (@comm_ring_presentation_direct_sum R P Q) P Q
    (@binary_products_proj1_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) P Q)
    (@binary_products_proj2_fapp0
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_freyd_binary_products R) P Q)
  ≡ @id (@CommRingFreydPresentation_cat R)
      (@comm_ring_presentation_direct_sum R P Q);

assert (R : τ CommRing)
  (X P Q : τ (@CommRingPresentation R)) ⊢
  @binary_products_pair_func
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_freyd_binary_products R) X P Q
  : τ (@Functor
      (Product_cat
        (Hom_cat (@CommRingFreydPresentation_cat R) X P)
        (Hom_cat (@CommRingFreydPresentation_cat R) X Q))
      (Hom_cat (@CommRingFreydPresentation_cat R) X
        (@comm_ring_presentation_direct_sum R P Q)));

assertnot (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R)) ⊢
  @binary_products_proj1_fapp0
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_freyd_binary_products R) P Q
  ≡ @comm_ring_freyd_zero_class R
      (@comm_ring_presentation_direct_sum R P Q) P;
