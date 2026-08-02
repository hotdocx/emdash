/*
  The closed two-element commutative ring F2.

  Its Boolean carrier, XOR addition, conjunction multiplication, and complete
  ring laws are constructed internally by finite Boolean elimination.  This
  model is rule-free reusable algebraic data; it declares no field-specific
  inverse interface, localization, topology, Spec, or scheme.
*/

require open emdash.emdash3_2_commutative_algebra;

// Internal finite elimination helpers for binary and ternary ring laws.
protected symbol f2_bool_elim2
  (P : τ Bool_grpd → τ Bool_grpd → Grpd)
  (pff : τ (P false false))
  (pft : τ (P false true))
  (ptf : τ (P true false))
  (ptt : τ (P true true))
  (x y : τ Bool_grpd)
  : τ (P x y)
≔ (@bool_elim
      (λ x0 : τ Bool_grpd,
        @Pi_grpd Bool_grpd (λ y0 : τ Bool_grpd, P x0 y0))
      (λ y0 : τ Bool_grpd,
        @bool_elim
          (λ y1 : τ Bool_grpd, P false y1)
          pff pft y0)
      (λ y0 : τ Bool_grpd,
        @bool_elim
          (λ y1 : τ Bool_grpd, P true y1)
          ptf ptt y0)
      x) y;

protected symbol f2_bool_elim3
  (P : τ Bool_grpd → τ Bool_grpd → τ Bool_grpd → Grpd)
  (pfff : τ (P false false false))
  (pfft : τ (P false false true))
  (pftf : τ (P false true false))
  (pftt : τ (P false true true))
  (ptff : τ (P true false false))
  (ptft : τ (P true false true))
  (pttf : τ (P true true false))
  (pttt : τ (P true true true))
  (x y z : τ Bool_grpd)
  : τ (P x y z)
≔ ((@bool_elim
      (λ x0 : τ Bool_grpd,
        @Pi_grpd Bool_grpd (λ y0 : τ Bool_grpd,
          @Pi_grpd Bool_grpd (λ z0 : τ Bool_grpd, P x0 y0 z0)))
      (λ y0 : τ Bool_grpd,
        λ z0 : τ Bool_grpd,
          @f2_bool_elim2
            (λ y1 : τ Bool_grpd,
              λ z1 : τ Bool_grpd, P false y1 z1)
            pfff pfft pftf pftt y0 z0)
      (λ y0 : τ Bool_grpd,
        λ z0 : τ Bool_grpd,
          @f2_bool_elim2
            (λ y1 : τ Bool_grpd,
              λ z1 : τ Bool_grpd, P true y1 z1)
            ptff ptft pttf pttt y0 z0)
      x) y) z;

// Boolean equality is proposition-valued by exhaustive internal elimination.
symbol f2_bool_is_set
  : τ (IsSetGrpd Bool_grpd)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      @f2_bool_elim2
        (λ x0 : τ Bool_grpd,
          λ y0 : τ Bool_grpd,
            IsPropGrpd (@= Bool_grpd x0 y0))
        unit_is_prop
        empty_is_prop
        empty_is_prop
        unit_is_prop
        x y;

// Boolean complement implements the second branch of XOR.
symbol f2_not
  (x : τ Bool_grpd)
  : τ Bool_grpd
≔ @bool_elim (λ _ : τ Bool_grpd, Bool_grpd) true false x;

symbol f2_add
  (x y : τ Bool_grpd)
  : τ Bool_grpd
≔ @bool_elim
    (λ _ : τ Bool_grpd, Bool_grpd)
    y
    (@f2_not y)
    x;

symbol f2_mul
  (x y : τ Bool_grpd)
  : τ Bool_grpd
≔ @bool_elim
    (λ _ : τ Bool_grpd, Bool_grpd)
    false
    y
    x;

// F2 has XOR addition, self-negation, and conjunction multiplication.
symbol f2_ops
  : τ (@CommRingOps Bool_grpd)
≔ @comm_ring_ops_intro
    Bool_grpd
    false true
    (λ x : τ Bool_grpd, λ y : τ Bool_grpd, @f2_add x y)
    (λ x : τ Bool_grpd, x)
    (λ x : τ Bool_grpd, λ y : τ Bool_grpd, @f2_mul x y);

symbol f2_add_assoc
  : τ (@CommRingAddAssoc Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      λ z : τ Bool_grpd,
        @f2_bool_elim3
          (λ x0 : τ Bool_grpd,
            λ y0 : τ Bool_grpd,
              λ z0 : τ Bool_grpd,
                @= Bool_grpd
                  (@f2_add (@f2_add x0 y0) z0)
                  (@f2_add x0 (@f2_add y0 z0)))
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd true)
          (@eq_refl Bool_grpd true)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd true)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd true)
          x y z;

symbol f2_add_comm
  : τ (@CommRingAddComm Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      @f2_bool_elim2
        (λ x0 : τ Bool_grpd,
          λ y0 : τ Bool_grpd,
            @= Bool_grpd (@f2_add x0 y0) (@f2_add y0 x0))
        (@eq_refl Bool_grpd false)
        (@eq_refl Bool_grpd true)
        (@eq_refl Bool_grpd true)
        (@eq_refl Bool_grpd false)
        x y;

symbol f2_add_zero
  : τ (@CommRingAddZero Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    @bool_elim
      (λ x0 : τ Bool_grpd,
        @= Bool_grpd (@f2_add x0 false) x0)
      (@eq_refl Bool_grpd false)
      (@eq_refl Bool_grpd true)
      x;

symbol f2_add_inv
  : τ (@CommRingAddInv Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    @bool_elim
      (λ x0 : τ Bool_grpd,
        @= Bool_grpd (@f2_add x0 x0) false)
      (@eq_refl Bool_grpd false)
      (@eq_refl Bool_grpd false)
      x;

symbol f2_mul_assoc
  : τ (@CommRingMulAssoc Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      λ z : τ Bool_grpd,
        @f2_bool_elim3
          (λ x0 : τ Bool_grpd,
            λ y0 : τ Bool_grpd,
              λ z0 : τ Bool_grpd,
                @= Bool_grpd
                  (@f2_mul (@f2_mul x0 y0) z0)
                  (@f2_mul x0 (@f2_mul y0 z0)))
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd true)
          x y z;

symbol f2_mul_comm
  : τ (@CommRingMulComm Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      @f2_bool_elim2
        (λ x0 : τ Bool_grpd,
          λ y0 : τ Bool_grpd,
            @= Bool_grpd (@f2_mul x0 y0) (@f2_mul y0 x0))
        (@eq_refl Bool_grpd false)
        (@eq_refl Bool_grpd false)
        (@eq_refl Bool_grpd false)
        (@eq_refl Bool_grpd true)
        x y;

symbol f2_mul_one
  : τ (@CommRingMulOne Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    @bool_elim
      (λ x0 : τ Bool_grpd,
        @= Bool_grpd (@f2_mul x0 true) x0)
      (@eq_refl Bool_grpd false)
      (@eq_refl Bool_grpd true)
      x;

symbol f2_left_distrib
  : τ (@CommRingLeftDistrib Bool_grpd f2_ops)
≔ λ x : τ Bool_grpd,
    λ y : τ Bool_grpd,
      λ z : τ Bool_grpd,
        @f2_bool_elim3
          (λ x0 : τ Bool_grpd,
            λ y0 : τ Bool_grpd,
              λ z0 : τ Bool_grpd,
                @= Bool_grpd
                  (@f2_mul x0 (@f2_add y0 z0))
                  (@f2_add (@f2_mul x0 y0) (@f2_mul x0 z0)))
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd false)
          (@eq_refl Bool_grpd true)
          (@eq_refl Bool_grpd true)
          (@eq_refl Bool_grpd false)
          x y z;

// The eight exhaustive proofs form the complete commutative-ring law package.
symbol f2_laws
  : τ (@IsCommRing Bool_grpd f2_ops)
≔ @comm_ring_laws_intro
    Bool_grpd f2_ops
    f2_add_assoc f2_add_comm f2_add_zero f2_add_inv
    f2_mul_assoc f2_mul_comm f2_mul_one f2_left_distrib;

symbol f2_set_package
  : τ SetU_grpd
≔ @Struct_trunc_grpd trunc_zero Bool_grpd f2_bool_is_set;

// The closed two-element commutative ring.
symbol f2_comm_ring
  : τ CommRing
≔ @comm_ring_intro
    f2_set_package
    (@comm_ring_structure_intro Bool_grpd f2_ops f2_laws);
