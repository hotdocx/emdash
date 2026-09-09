/* The ordinary-profile evidence is derived and filled inside the model API. */
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cones;

assert (R : τ CommRing) ⊢
  @ncat_carrier (cat_succ cat_zero) (@comm_ring_freyd_one_cat R)
  ≡ @CommRingFreydPresentation_cat R;

assert [R : τ CommRing] (A : τ (@CommRingPresentation R))
  (d : τ (Functor WalkingArrow_cat (@CommRingFreydPresentation_cat R)))
  (h : τ (@Transf WalkingArrow_cat (@CommRingFreydPresentation_cat R)
    (@fapp0 (@CommRingFreydPresentation_cat R) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
      (@terminal_arrow_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) A) d)) ⊢
  @tapp0_fapp0 _ _ _ _
    (@zero_arrow_cone_obj (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) A d h)
    (@freyd_zero_cone_universal_transf R)
  ≡ h;

// Arbitrary directed 2-cells in this concrete target are quotient paths.
assert [R : τ CommRing] (P Q : τ (@CommRingPresentation R))
  (f g : τ (Hom (@CommRingFreydPresentation_cat R) P Q))
  (alpha : τ (Hom (Hom_cat (@CommRingFreydPresentation_cat R) P Q) f g)) ⊢
  alpha : τ (@= (@CommRingFreydHomSet R P Q) f g);

// Not an arbitrary-category cell-to-equality coercion.
assertnot (C : Cat) (x y : τ (Obj C)) (f g : τ (Hom C x y))
  (alpha : τ (Hom (Hom_cat C x y) f g)) ⊢
  alpha : τ (@= (Hom C x y) f g);

// The same direct conversion holds for the existing native square fibre.
assert [R : τ CommRing]
  [A0 A1 B0 B1 : τ (@CommRingPresentation R)]
  (u : τ (Hom (@CommRingFreydPresentation_cat R) A0 B0))
  (v : τ (Hom (@CommRingFreydPresentation_cat R) A1 B1))
  (a : τ (Hom (@CommRingFreydPresentation_cat R) A0 A1))
  (b : τ (Hom (@CommRingFreydPresentation_cat R) B0 B1))
  (alpha : τ (Obj (@homdc_fibre
    (@CommRingFreydPresentation_cat R) (@CommRingFreydPresentation_cat R)
    (@hom_int (@CommRingFreydPresentation_cat R) (@CommRingFreydPresentation_cat R)
      (@id_func (@CommRingFreydPresentation_cat R)))
    A0 A1 B0 B1 u v a b)))
  ⊢ alpha : τ (@= (@CommRingFreydHomSet R A0 B1)
      (@comp_fapp0 (@CommRingFreydPresentation_cat R) A0 B0 B1 b u)
      (@comp_fapp0 (@CommRingFreydPresentation_cat R) A0 A1 B1 v a));

require open emdash.emdash3_2_zero_arrow_cone_homology;

/* Identity at the concrete Freyd target; no profile argument supplied. */
assert (R : τ CommRing) (S : τ (@PreadditiveCategory (@CommRingFreydPresentation_cat R)))
  (T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)))
  (W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) S)) (V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) S))
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) S (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W))
  (Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) S (@comm_ring_zero_presentation R) T0 V))
  (z : τ (Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_homology_func (@CommRingFreydPresentation_cat R) S (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) T0 W V P Q) z z (@id (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) z)
  ≡ @id (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_homology_func (@CommRingFreydPresentation_cat R) S (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) T0 W V P Q) z);
