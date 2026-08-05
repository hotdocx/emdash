/*
  Universal-property localization at an idempotent through its fixed image.

  For e^2=e in R, the set-valued subtype eR = {x : R | e*x=x} inherits a
  commutative-ring structure with unit e.  Multiplication by e gives a
  structured map R -> eR.  If h:R->S makes h(e) invertible, then h(e) is both
  invertible and idempotent, hence equals one; restriction of h to the fixed
  subtype is consequently the unique localization factor.

  The resulting selected R[1/e] has computing carrier, operations, structure
  map, and factor map.  The construction is rule-free and quotient-free; all
  functoriality remains with CommRing_cat and the generic category owners.  It
  can be genuinely nondegenerate when supplied a nontrivial idempotent, but
  this module itself constructs neither product rings nor a closed nontrivial
  idempotent.  It declares no presheaf, topology, Spec, or scheme interface.
*/

require open emdash.emdash3_2_commutative_algebra_localization_zero;

symbol CommRingIdempotentImageCarrier
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  : Grpd
≔ `Σ_ x : τ (@comm_ring_carrier R),
    @= (@comm_ring_carrier R) (@comm_ring_mul R e x) x;

symbol comm_ring_idempotent_image_intro
  [R : τ CommRing]
  [e : τ (@comm_ring_carrier R)]
  (x : τ (@comm_ring_carrier R))
  (fixed : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @Struct_sigma
    (@comm_ring_carrier R)
    (λ y : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier R) (@comm_ring_mul R e y) y)
    x fixed;

symbol comm_ring_idempotent_image_element
  [R : τ CommRing]
  [e : τ (@comm_ring_carrier R)]
  (x : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@comm_ring_carrier R)
≔ sigma_Fst x;

symbol comm_ring_idempotent_image_fixed_path
  [R : τ CommRing]
  [e : τ (@comm_ring_carrier R)]
  (x : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e
        (@comm_ring_idempotent_image_element R e x))
      (@comm_ring_idempotent_image_element R e x))
≔ sigma_Snd x;

symbol comm_ring_idempotent_image_fixed_is_prop
  (R : τ CommRing)
  (e x : τ (@comm_ring_carrier R))
  : τ (IsPropGrpd (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x))
≔ (@comm_ring_carrier_is_set R) (@comm_ring_mul R e x) x;

symbol comm_ring_idempotent_image_carrier_is_set
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  : τ (IsSetGrpd (@CommRingIdempotentImageCarrier R e))
≔ @is_trunc_sigma
    trunc_zero
    (@comm_ring_carrier R)
    (λ x : τ (@comm_ring_carrier R),
      @= (@comm_ring_carrier R) (@comm_ring_mul R e x) x)
    (@comm_ring_carrier_is_set R)
    (λ x : τ (@comm_ring_carrier R),
      @prop_is_trunc_succ
        trunc_minus_one
        (@= (@comm_ring_carrier R) (@comm_ring_mul R e x) x)
        (@comm_ring_idempotent_image_fixed_is_prop R e x));

symbol comm_ring_idempotent_image_fixed_pathover
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  [x y : τ (@comm_ring_carrier R)]
  (fixed_x : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x))
  (fixed_y : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e y) y))
  (p : τ (@= (@comm_ring_carrier R) x y))
  : τ (@PathOver
      (@comm_ring_carrier R)
      (λ z : τ (@comm_ring_carrier R),
        @= (@comm_ring_carrier R) (@comm_ring_mul R e z) z)
      x y p fixed_x fixed_y)
≔ @ind_eqr
    (@comm_ring_carrier R)
    y
    (λ x0 : τ (@comm_ring_carrier R),
      λ p0 : τ (@= (@comm_ring_carrier R) x0 y),
        @Pi_grpd
          (@= (@comm_ring_carrier R) (@comm_ring_mul R e x0) x0)
          (λ fixed_x0 : τ (@= (@comm_ring_carrier R)
              (@comm_ring_mul R e x0) x0),
            @PathOver
              (@comm_ring_carrier R)
              (λ z : τ (@comm_ring_carrier R),
                @= (@comm_ring_carrier R) (@comm_ring_mul R e z) z)
              x0 y p0 fixed_x0 fixed_y))
    (λ fixed_x0 : τ (@= (@comm_ring_carrier R)
        (@comm_ring_mul R e y) y),
      @is_contr_center
        (@= (@= (@comm_ring_carrier R) (@comm_ring_mul R e y) y)
          fixed_x0 fixed_y)
        ((@comm_ring_idempotent_image_fixed_is_prop R e y)
          fixed_x0 fixed_y))
    x p fixed_x;

symbol comm_ring_idempotent_image_ext
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  [x y : τ (@CommRingIdempotentImageCarrier R e)]
  (p : τ (@= (@comm_ring_carrier R)
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y)))
  : τ (@= (@CommRingIdempotentImageCarrier R e) x y)
≔ @Struct_sigma
    (@= (@comm_ring_carrier R)
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y))
    (λ q : τ (@= (@comm_ring_carrier R)
        (@comm_ring_idempotent_image_element R e x)
        (@comm_ring_idempotent_image_element R e y)),
      @PathOver
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R),
          @= (@comm_ring_carrier R) (@comm_ring_mul R e z) z)
        (@comm_ring_idempotent_image_element R e x)
        (@comm_ring_idempotent_image_element R e y)
        q
        (@comm_ring_idempotent_image_fixed_path R e x)
        (@comm_ring_idempotent_image_fixed_path R e y))
    p
    (@comm_ring_idempotent_image_fixed_pathover
      R e
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y)
      (@comm_ring_idempotent_image_fixed_path R e x)
      (@comm_ring_idempotent_image_fixed_path R e y)
      p);

// The retained right additive unit law derives its left-handed mate.
protected symbol comm_ring_idempotent_image_add_zero_left
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R (@comm_ring_zero R) x) x)
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_add R (@comm_ring_zero R) x)
    (@comm_ring_add R x (@comm_ring_zero R))
    x
    ((@comm_ring_add_comm_law R) (@comm_ring_zero R) x)
    ((@comm_ring_add_zero_law R) x);

// Any b with a+b=0 is the selected additive inverse -a.
protected symbol comm_ring_idempotent_image_add_inverse_unique
  (R : τ CommRing)
  (a b : τ (@comm_ring_carrier R))
  (inverse_law : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R a b) (@comm_ring_zero R)))
  : τ (@= (@comm_ring_carrier R) b (@comm_ring_neg R a))
≔ @eq_trans
    (@comm_ring_carrier R)
    b
    (@comm_ring_add R (@comm_ring_zero R) b)
    (@comm_ring_neg R a)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_add R (@comm_ring_zero R) b)
      b
      (@comm_ring_idempotent_image_add_zero_left R b))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R (@comm_ring_zero R) b)
      (@comm_ring_add R
        (@comm_ring_add R a (@comm_ring_neg R a)) b)
      (@comm_ring_neg R a)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_add R z b)
        (@comm_ring_zero R)
        (@comm_ring_add R a (@comm_ring_neg R a))
        (@eq_sym
          (@comm_ring_carrier R)
          (@comm_ring_add R a (@comm_ring_neg R a))
          (@comm_ring_zero R)
          ((@comm_ring_add_inv_law R) a)))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_add R
          (@comm_ring_add R a (@comm_ring_neg R a)) b)
        (@comm_ring_add R
          (@comm_ring_add R (@comm_ring_neg R a) a) b)
        (@comm_ring_neg R a)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ z : τ (@comm_ring_carrier R), @comm_ring_add R z b)
          (@comm_ring_add R a (@comm_ring_neg R a))
          (@comm_ring_add R (@comm_ring_neg R a) a)
          ((@comm_ring_add_comm_law R) a (@comm_ring_neg R a)))
        (@eq_trans
          (@comm_ring_carrier R)
          (@comm_ring_add R
            (@comm_ring_add R (@comm_ring_neg R a) a) b)
          (@comm_ring_add R
            (@comm_ring_neg R a) (@comm_ring_add R a b))
          (@comm_ring_neg R a)
          ((@comm_ring_add_assoc_law R) (@comm_ring_neg R a) a b)
          (@eq_trans
            (@comm_ring_carrier R)
            (@comm_ring_add R
              (@comm_ring_neg R a) (@comm_ring_add R a b))
            (@comm_ring_add R (@comm_ring_neg R a) (@comm_ring_zero R))
            (@comm_ring_neg R a)
            (@eq_ap
              (@comm_ring_carrier R)
              (@comm_ring_carrier R)
              (λ z : τ (@comm_ring_carrier R),
                @comm_ring_add R (@comm_ring_neg R a) z)
              (@comm_ring_add R a b)
              (@comm_ring_zero R)
              inverse_law)
            ((@comm_ring_add_zero_law R) (@comm_ring_neg R a))))));

// Multiplication preserves the selected additive inverse on the right.
protected symbol comm_ring_idempotent_image_mul_neg_right
  (R : τ CommRing)
  (a b : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R a (@comm_ring_neg R b))
      (@comm_ring_neg R (@comm_ring_mul R a b)))
≔ @comm_ring_idempotent_image_add_inverse_unique
    R
    (@comm_ring_mul R a b)
    (@comm_ring_mul R a (@comm_ring_neg R b))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R a b)
        (@comm_ring_mul R a (@comm_ring_neg R b)))
      (@comm_ring_mul R a
        (@comm_ring_add R b (@comm_ring_neg R b)))
      (@comm_ring_zero R)
      (@eq_sym
        (@comm_ring_carrier R)
        (@comm_ring_mul R a
          (@comm_ring_add R b (@comm_ring_neg R b)))
        (@comm_ring_add R
          (@comm_ring_mul R a b)
          (@comm_ring_mul R a (@comm_ring_neg R b)))
        ((@comm_ring_left_distrib_law R) a b (@comm_ring_neg R b)))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R a
          (@comm_ring_add R b (@comm_ring_neg R b)))
        (@comm_ring_mul R a (@comm_ring_zero R))
        (@comm_ring_zero R)
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R a z)
          (@comm_ring_add R b (@comm_ring_neg R b))
          (@comm_ring_zero R)
          ((@comm_ring_add_inv_law R) b))
        (@comm_ring_mul_zero_right R a)));

symbol comm_ring_idempotent_image_zero_fixed
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e (@comm_ring_zero R))
      (@comm_ring_zero R))
≔ @comm_ring_mul_zero_right R e;

symbol comm_ring_idempotent_image_add_fixed
  (R : τ CommRing)
  (e x y : τ (@comm_ring_carrier R))
  (fixed_x : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x))
  (fixed_y : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e y) y))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e (@comm_ring_add R x y))
      (@comm_ring_add R x y))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R e (@comm_ring_add R x y))
    (@comm_ring_add R
      (@comm_ring_mul R e x) (@comm_ring_mul R e y))
    (@comm_ring_add R x y)
    ((@comm_ring_left_distrib_law R) e x y)
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R e x) (@comm_ring_mul R e y))
      (@comm_ring_add R x (@comm_ring_mul R e y))
      (@comm_ring_add R x y)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R),
          @comm_ring_add R z (@comm_ring_mul R e y))
        (@comm_ring_mul R e x) x fixed_x)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_add R x z)
        (@comm_ring_mul R e y) y fixed_y));

symbol comm_ring_idempotent_image_neg_fixed
  (R : τ CommRing)
  (e x : τ (@comm_ring_carrier R))
  (fixed_x : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e (@comm_ring_neg R x))
      (@comm_ring_neg R x))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R e (@comm_ring_neg R x))
    (@comm_ring_neg R (@comm_ring_mul R e x))
    (@comm_ring_neg R x)
    (@comm_ring_idempotent_image_mul_neg_right R e x)
    (@eq_ap
      (@comm_ring_carrier R)
      (@comm_ring_carrier R)
      (λ z : τ (@comm_ring_carrier R), @comm_ring_neg R z)
      (@comm_ring_mul R e x) x fixed_x);

symbol comm_ring_idempotent_image_mul_fixed
  (R : τ CommRing)
  (e x y : τ (@comm_ring_carrier R))
  (fixed_x : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e x) x))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e (@comm_ring_mul R x y))
      (@comm_ring_mul R x y))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R e (@comm_ring_mul R x y))
    (@comm_ring_mul R (@comm_ring_mul R e x) y)
    (@comm_ring_mul R x y)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_mul R e x) y)
      (@comm_ring_mul R e (@comm_ring_mul R x y))
      ((@comm_ring_mul_assoc_law R) e x y))
    (@eq_ap
      (@comm_ring_carrier R)
      (@comm_ring_carrier R)
      (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R z y)
      (@comm_ring_mul R e x) x fixed_x);

symbol comm_ring_idempotent_image_zero
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @comm_ring_idempotent_image_intro
    R e (@comm_ring_zero R)
    (@comm_ring_idempotent_image_zero_fixed R e);

symbol comm_ring_idempotent_image_one
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @comm_ring_idempotent_image_intro R e e idempotent;

symbol comm_ring_idempotent_image_add
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (x y : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @comm_ring_idempotent_image_intro
    R e
    (@comm_ring_add R
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y))
    (@comm_ring_idempotent_image_add_fixed
      R e
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y)
      (@comm_ring_idempotent_image_fixed_path R e x)
      (@comm_ring_idempotent_image_fixed_path R e y));

symbol comm_ring_idempotent_image_neg
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (x : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @comm_ring_idempotent_image_intro
    R e
    (@comm_ring_neg R (@comm_ring_idempotent_image_element R e x))
    (@comm_ring_idempotent_image_neg_fixed
      R e
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_fixed_path R e x));

symbol comm_ring_idempotent_image_mul
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (x y : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @comm_ring_idempotent_image_intro
    R e
    (@comm_ring_mul R
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y))
    (@comm_ring_idempotent_image_mul_fixed
      R e
      (@comm_ring_idempotent_image_element R e x)
      (@comm_ring_idempotent_image_element R e y)
      (@comm_ring_idempotent_image_fixed_path R e x));

symbol comm_ring_idempotent_image_set_package
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  : τ SetU_grpd
≔ @Struct_trunc_grpd
    trunc_zero
    (@CommRingIdempotentImageCarrier R e)
    (@comm_ring_idempotent_image_carrier_is_set R e);

symbol comm_ring_idempotent_image_ops
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingOps (@CommRingIdempotentImageCarrier R e))
≔ @comm_ring_ops_intro
    (@CommRingIdempotentImageCarrier R e)
    (@comm_ring_idempotent_image_zero R e)
    (@comm_ring_idempotent_image_one R e idempotent)
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        @comm_ring_idempotent_image_add R e x y)
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      @comm_ring_idempotent_image_neg R e x)
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        @comm_ring_idempotent_image_mul R e x y);

symbol comm_ring_idempotent_image_mul_one_path
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (x : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_idempotent_image_element R e x) e)
      (@comm_ring_idempotent_image_element R e x))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R
      (@comm_ring_idempotent_image_element R e x) e)
    (@comm_ring_mul R
      e (@comm_ring_idempotent_image_element R e x))
    (@comm_ring_idempotent_image_element R e x)
    ((@comm_ring_mul_comm_law R)
      (@comm_ring_idempotent_image_element R e x) e)
    (@comm_ring_idempotent_image_fixed_path R e x);

symbol comm_ring_idempotent_image_laws
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@IsCommRing
      (@CommRingIdempotentImageCarrier R e)
      (@comm_ring_idempotent_image_ops R e idempotent))
≔ @comm_ring_laws_intro
    (@CommRingIdempotentImageCarrier R e)
    (@comm_ring_idempotent_image_ops R e idempotent)
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        λ z : τ (@CommRingIdempotentImageCarrier R e),
          @comm_ring_idempotent_image_ext
            R e _ _
            ((@comm_ring_add_assoc_law R)
              (@comm_ring_idempotent_image_element R e x)
              (@comm_ring_idempotent_image_element R e y)
              (@comm_ring_idempotent_image_element R e z)))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        @comm_ring_idempotent_image_ext
          R e _ _
          ((@comm_ring_add_comm_law R)
            (@comm_ring_idempotent_image_element R e x)
            (@comm_ring_idempotent_image_element R e y)))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      @comm_ring_idempotent_image_ext
        R e _ _
        ((@comm_ring_add_zero_law R)
          (@comm_ring_idempotent_image_element R e x)))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      @comm_ring_idempotent_image_ext
        R e _ _
        ((@comm_ring_add_inv_law R)
          (@comm_ring_idempotent_image_element R e x)))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        λ z : τ (@CommRingIdempotentImageCarrier R e),
          @comm_ring_idempotent_image_ext
            R e _ _
            ((@comm_ring_mul_assoc_law R)
              (@comm_ring_idempotent_image_element R e x)
              (@comm_ring_idempotent_image_element R e y)
              (@comm_ring_idempotent_image_element R e z)))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        @comm_ring_idempotent_image_ext
          R e _ _
          ((@comm_ring_mul_comm_law R)
            (@comm_ring_idempotent_image_element R e x)
            (@comm_ring_idempotent_image_element R e y)))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      @comm_ring_idempotent_image_ext
        R e _ _
        (@comm_ring_idempotent_image_mul_one_path R e x))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        λ z : τ (@CommRingIdempotentImageCarrier R e),
          @comm_ring_idempotent_image_ext
            R e _ _
            ((@comm_ring_left_distrib_law R)
              (@comm_ring_idempotent_image_element R e x)
              (@comm_ring_idempotent_image_element R e y)
              (@comm_ring_idempotent_image_element R e z)));

symbol comm_ring_idempotent_image_structure
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingStructure (@CommRingIdempotentImageCarrier R e))
≔ @comm_ring_structure_intro
    (@CommRingIdempotentImageCarrier R e)
    (@comm_ring_idempotent_image_ops R e idempotent)
    (@comm_ring_idempotent_image_laws R e idempotent);

symbol comm_ring_idempotent_image
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ CommRing
≔ @comm_ring_intro
    (@comm_ring_idempotent_image_set_package R e)
    (@comm_ring_idempotent_image_structure R e idempotent);

// Multiplication by e lands in the fixed-point subtype.
symbol comm_ring_idempotent_image_scale_fixed
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e (@comm_ring_mul R e x))
      (@comm_ring_mul R e x))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R e (@comm_ring_mul R e x))
    (@comm_ring_mul R (@comm_ring_mul R e e) x)
    (@comm_ring_mul R e x)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_mul R e e) x)
      (@comm_ring_mul R e (@comm_ring_mul R e x))
      ((@comm_ring_mul_assoc_law R) e e x))
    (@eq_ap
      (@comm_ring_carrier R)
      (@comm_ring_carrier R)
      (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R z x)
      (@comm_ring_mul R e e) e idempotent);

symbol comm_ring_idempotent_image_scale
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x : τ (@comm_ring_carrier R))
  : τ (@CommRingIdempotentImageCarrier R e)
≔ @comm_ring_idempotent_image_intro
    R e
    (@comm_ring_mul R e x)
    (@comm_ring_idempotent_image_scale_fixed R e idempotent x);

// The idempotent scaling map preserves multiplication.
protected symbol comm_ring_idempotent_image_scale_mul_reverse
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x y : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_mul R e x)
        (@comm_ring_mul R e y))
      (@comm_ring_mul R e (@comm_ring_mul R x y)))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R
      (@comm_ring_mul R e x)
      (@comm_ring_mul R e y))
    (@comm_ring_mul R
      (@comm_ring_mul R (@comm_ring_mul R e x) e) y)
    (@comm_ring_mul R e (@comm_ring_mul R x y))
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_mul R (@comm_ring_mul R e x) e) y)
      (@comm_ring_mul R
        (@comm_ring_mul R e x)
        (@comm_ring_mul R e y))
      ((@comm_ring_mul_assoc_law R)
        (@comm_ring_mul R e x) e y))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R
        (@comm_ring_mul R (@comm_ring_mul R e x) e) y)
      (@comm_ring_mul R
        (@comm_ring_mul R e (@comm_ring_mul R e x)) y)
      (@comm_ring_mul R e (@comm_ring_mul R x y))
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R z y)
        (@comm_ring_mul R (@comm_ring_mul R e x) e)
        (@comm_ring_mul R e (@comm_ring_mul R e x))
        ((@comm_ring_mul_comm_law R) (@comm_ring_mul R e x) e))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R
          (@comm_ring_mul R e (@comm_ring_mul R e x)) y)
        (@comm_ring_mul R
          (@comm_ring_mul R (@comm_ring_mul R e e) x) y)
        (@comm_ring_mul R e (@comm_ring_mul R x y))
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R z y)
          (@comm_ring_mul R e (@comm_ring_mul R e x))
          (@comm_ring_mul R (@comm_ring_mul R e e) x)
          (@eq_sym
            (@comm_ring_carrier R)
            (@comm_ring_mul R (@comm_ring_mul R e e) x)
            (@comm_ring_mul R e (@comm_ring_mul R e x))
            ((@comm_ring_mul_assoc_law R) e e x)))
        (@eq_trans
          (@comm_ring_carrier R)
          (@comm_ring_mul R
            (@comm_ring_mul R (@comm_ring_mul R e e) x) y)
          (@comm_ring_mul R (@comm_ring_mul R e x) y)
          (@comm_ring_mul R e (@comm_ring_mul R x y))
          (@eq_ap
            (@comm_ring_carrier R)
            (@comm_ring_carrier R)
            (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R z y)
            (@comm_ring_mul R (@comm_ring_mul R e e) x)
            (@comm_ring_mul R e x)
            (@eq_ap
              (@comm_ring_carrier R)
              (@comm_ring_carrier R)
              (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R z x)
              (@comm_ring_mul R e e) e idempotent))
          ((@comm_ring_mul_assoc_law R) e x y))));

symbol comm_ring_idempotent_image_scale_mul
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x y : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e (@comm_ring_mul R x y))
      (@comm_ring_mul R
        (@comm_ring_mul R e x)
        (@comm_ring_mul R e y)))
≔ @eq_sym
    (@comm_ring_carrier R)
    (@comm_ring_mul R
      (@comm_ring_mul R e x)
      (@comm_ring_mul R e y))
    (@comm_ring_mul R e (@comm_ring_mul R x y))
    (@comm_ring_idempotent_image_scale_mul_reverse
      R e idempotent x y);

symbol comm_ring_idempotent_image_localization_laws
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingHomLaws
      R
      (@comm_ring_idempotent_image R e idempotent)
      (λ x : τ (@comm_ring_carrier R),
        @comm_ring_idempotent_image_scale R e idempotent x))
≔ @comm_ring_hom_laws_intro
    R
    (@comm_ring_idempotent_image R e idempotent)
    (λ x : τ (@comm_ring_carrier R),
      @comm_ring_idempotent_image_scale R e idempotent x)
    (@comm_ring_idempotent_image_ext
      R e _ _
      (@comm_ring_mul_zero_right R e))
    (@comm_ring_idempotent_image_ext
      R e _ _
      ((@comm_ring_mul_one_law R) e))
    (λ x : τ (@comm_ring_carrier R),
      λ y : τ (@comm_ring_carrier R),
        @comm_ring_idempotent_image_ext
          R e _ _
          ((@comm_ring_left_distrib_law R) e x y))
    (λ x : τ (@comm_ring_carrier R),
      @comm_ring_idempotent_image_ext
        R e _ _
        (@comm_ring_idempotent_image_mul_neg_right R e x))
    (λ x : τ (@comm_ring_carrier R),
      λ y : τ (@comm_ring_carrier R),
        @comm_ring_idempotent_image_ext
          R e _ _
          (@comm_ring_idempotent_image_scale_mul R e idempotent x y));

symbol comm_ring_idempotent_image_localization_map
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingHom R
      (@comm_ring_idempotent_image R e idempotent))
≔ @comm_ring_hom_intro
    R
    (@comm_ring_idempotent_image R e idempotent)
    (λ x : τ (@comm_ring_carrier R),
      @comm_ring_idempotent_image_scale R e idempotent x)
    (@comm_ring_idempotent_image_localization_laws R e idempotent);

symbol comm_ring_idempotent_image_localization_e_is_one
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@=
      (@comm_ring_carrier
        (@comm_ring_idempotent_image R e idempotent))
      (@comm_ring_hom_apply
        R
        (@comm_ring_idempotent_image R e idempotent)
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        e)
      (@comm_ring_one
        (@comm_ring_idempotent_image R e idempotent)))
≔ @comm_ring_idempotent_image_ext R e _ _ idempotent;

// An invertible idempotent is the multiplicative identity.
symbol comm_ring_unit_idempotent_is_one
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R a a) a))
  (unit : τ (@CommRingUnitEvidence R a))
  : τ (@= (@comm_ring_carrier R) a (@comm_ring_one R))
≔ @eq_trans
    (@comm_ring_carrier R)
    a
    (@comm_ring_mul R a (@comm_ring_one R))
    (@comm_ring_one R)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_mul R a (@comm_ring_one R))
      a
      ((@comm_ring_mul_one_law R) a))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R a (@comm_ring_one R))
      (@comm_ring_mul R a
        (@comm_ring_mul R a (@comm_ring_unit_inverse R a unit)))
      (@comm_ring_one R)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R a z)
        (@comm_ring_one R)
        (@comm_ring_mul R a (@comm_ring_unit_inverse R a unit))
        (@eq_sym
          (@comm_ring_carrier R)
          (@comm_ring_mul R a (@comm_ring_unit_inverse R a unit))
          (@comm_ring_one R)
          (@comm_ring_unit_law R a unit)))
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_mul R a
          (@comm_ring_mul R a (@comm_ring_unit_inverse R a unit)))
        (@comm_ring_mul R
          (@comm_ring_mul R a a)
          (@comm_ring_unit_inverse R a unit))
        (@comm_ring_one R)
        (@eq_sym
          (@comm_ring_carrier R)
          (@comm_ring_mul R
            (@comm_ring_mul R a a)
            (@comm_ring_unit_inverse R a unit))
          (@comm_ring_mul R a
            (@comm_ring_mul R a (@comm_ring_unit_inverse R a unit)))
          ((@comm_ring_mul_assoc_law R)
            a a (@comm_ring_unit_inverse R a unit)))
        (@eq_trans
          (@comm_ring_carrier R)
          (@comm_ring_mul R
            (@comm_ring_mul R a a)
            (@comm_ring_unit_inverse R a unit))
          (@comm_ring_mul R a (@comm_ring_unit_inverse R a unit))
          (@comm_ring_one R)
          (@eq_ap
            (@comm_ring_carrier R)
            (@comm_ring_carrier R)
            (λ z : τ (@comm_ring_carrier R),
              @comm_ring_mul R z (@comm_ring_unit_inverse R a unit))
            (@comm_ring_mul R a a) a idempotent)
          (@comm_ring_unit_law R a unit))));

symbol comm_ring_hom_idempotent_image_path
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_mul S
        (@comm_ring_hom_apply R S h e)
        (@comm_ring_hom_apply R S h e))
      (@comm_ring_hom_apply R S h e))
≔ @eq_trans
    (@comm_ring_carrier S)
    (@comm_ring_mul S
      (@comm_ring_hom_apply R S h e)
      (@comm_ring_hom_apply R S h e))
    (@comm_ring_hom_apply R S h (@comm_ring_mul R e e))
    (@comm_ring_hom_apply R S h e)
    (@eq_sym
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h (@comm_ring_mul R e e))
      (@comm_ring_mul S
        (@comm_ring_hom_apply R S h e)
        (@comm_ring_hom_apply R S h e))
      ((@comm_ring_hom_mul_law R S h) e e))
    (@eq_ap
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_hom_function R S h)
      (@comm_ring_mul R e e) e idempotent);

symbol comm_ring_hom_idempotent_unit_is_one
  [R S : τ CommRing]
  (h : τ (@CommRingHom R S))
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  : τ (@= (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h e)
      (@comm_ring_one S))
≔ @comm_ring_unit_idempotent_is_one
    S
    (@comm_ring_hom_apply R S h e)
    (@comm_ring_hom_idempotent_image_path R S h e idempotent)
    unit;

protected symbol comm_ring_idempotent_image_mul_one_left
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_one R) x) x)
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R (@comm_ring_one R) x)
    (@comm_ring_mul R x (@comm_ring_one R))
    x
    ((@comm_ring_mul_comm_law R) (@comm_ring_one R) x)
    ((@comm_ring_mul_one_law R) x);

symbol comm_ring_idempotent_image_factor_laws
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  : τ (@CommRingHomLaws
      (@comm_ring_idempotent_image R e idempotent)
      S
      (λ x : τ (@CommRingIdempotentImageCarrier R e),
        @comm_ring_hom_apply R S h
          (@comm_ring_idempotent_image_element R e x)))
≔ @comm_ring_hom_laws_intro
    (@comm_ring_idempotent_image R e idempotent)
    S
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      @comm_ring_hom_apply R S h
        (@comm_ring_idempotent_image_element R e x))
    (@comm_ring_hom_zero_law R S h)
    (@comm_ring_hom_idempotent_unit_is_one R S h e idempotent unit)
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        (@comm_ring_hom_add_law R S h)
          (@comm_ring_idempotent_image_element R e x)
          (@comm_ring_idempotent_image_element R e y))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      (@comm_ring_hom_neg_law R S h)
        (@comm_ring_idempotent_image_element R e x))
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      λ y : τ (@CommRingIdempotentImageCarrier R e),
        (@comm_ring_hom_mul_law R S h)
          (@comm_ring_idempotent_image_element R e x)
          (@comm_ring_idempotent_image_element R e y));

symbol comm_ring_idempotent_image_factor_map
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  : τ (@CommRingHom
      (@comm_ring_idempotent_image R e idempotent) S)
≔ @comm_ring_hom_intro
    (@comm_ring_idempotent_image R e idempotent)
    S
    (λ x : τ (@CommRingIdempotentImageCarrier R e),
      @comm_ring_hom_apply R S h
        (@comm_ring_idempotent_image_element R e x))
    (@comm_ring_idempotent_image_factor_laws
      R e idempotent S h unit);

symbol comm_ring_idempotent_image_factor_agreement
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  : τ (@CommRingLocalizationAgreement
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      (@comm_ring_idempotent_image_factor_map
        R e idempotent S h unit)
      h)
≔ λ x : τ (@comm_ring_carrier R),
    @eq_trans
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h (@comm_ring_mul R e x))
      (@comm_ring_mul S
        (@comm_ring_hom_apply R S h e)
        (@comm_ring_hom_apply R S h x))
      (@comm_ring_hom_apply R S h x)
      ((@comm_ring_hom_mul_law R S h) e x)
      (@eq_trans
        (@comm_ring_carrier S)
        (@comm_ring_mul S
          (@comm_ring_hom_apply R S h e)
          (@comm_ring_hom_apply R S h x))
        (@comm_ring_mul S
          (@comm_ring_one S)
          (@comm_ring_hom_apply R S h x))
        (@comm_ring_hom_apply R S h x)
        (@eq_ap
          (@comm_ring_carrier S)
          (@comm_ring_carrier S)
          (λ z : τ (@comm_ring_carrier S),
            @comm_ring_mul S z (@comm_ring_hom_apply R S h x))
          (@comm_ring_hom_apply R S h e)
          (@comm_ring_one S)
          (@comm_ring_hom_idempotent_unit_is_one
            R S h e idempotent unit))
        (@comm_ring_idempotent_image_mul_one_left
          S (@comm_ring_hom_apply R S h x)));

symbol comm_ring_idempotent_image_factor_center
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h)
≔ @comm_ring_localization_factor_intro
    R
    (@comm_ring_idempotent_image R e idempotent)
    S
    (@comm_ring_idempotent_image_localization_map R e idempotent)
    h
    (@comm_ring_idempotent_image_factor_map R e idempotent S h unit)
    (@comm_ring_idempotent_image_factor_agreement
      R e idempotent S h unit);

// Scaling a fixed point returns that same subtype element.
symbol comm_ring_idempotent_image_scale_retract
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (x : τ (@CommRingIdempotentImageCarrier R e))
  : τ (@=
      (@comm_ring_carrier
        (@comm_ring_idempotent_image R e idempotent))
      (@comm_ring_hom_apply
        R
        (@comm_ring_idempotent_image R e idempotent)
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        (@comm_ring_idempotent_image_element R e x))
      x)
≔ @comm_ring_idempotent_image_ext
    R e _ _
    (@comm_ring_idempotent_image_fixed_path R e x);

symbol comm_ring_idempotent_image_competitor_pointwise
  [R S : τ CommRing]
  [e : τ (@comm_ring_carrier R)]
  [idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)]
  [h : τ (@CommRingHom R S)]
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  (candidate : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h))
  : τ (@CommRingHomPointwisePath
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_factor_map
        R e idempotent S h unit)
      (@comm_ring_localization_factor_map
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h
        candidate))
≔ λ x : τ (@CommRingIdempotentImageCarrier R e),
    @eq_trans
      (@comm_ring_carrier S)
      (@comm_ring_hom_apply R S h
        (@comm_ring_idempotent_image_element R e x))
      (@comm_ring_hom_apply
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_localization_factor_map
          R
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          h
          candidate)
        (@comm_ring_hom_apply
          R
          (@comm_ring_idempotent_image R e idempotent)
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          (@comm_ring_idempotent_image_element R e x)))
      (@comm_ring_hom_apply
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_localization_factor_map
          R
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          h
          candidate)
        x)
      (@eq_sym
        (@comm_ring_carrier S)
        (@comm_ring_hom_apply
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_localization_factor_map
            R
            (@comm_ring_idempotent_image R e idempotent)
            S
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            h
            candidate)
          (@comm_ring_hom_apply
            R
            (@comm_ring_idempotent_image R e idempotent)
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            (@comm_ring_idempotent_image_element R e x)))
        (@comm_ring_hom_apply R S h
          (@comm_ring_idempotent_image_element R e x))
        ((@comm_ring_localization_factor_agreement
            R
            (@comm_ring_idempotent_image R e idempotent)
            S
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            h
            candidate)
          (@comm_ring_idempotent_image_element R e x)))
      (@eq_ap
        (@comm_ring_carrier
          (@comm_ring_idempotent_image R e idempotent))
        (@comm_ring_carrier S)
        (@comm_ring_hom_function
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_localization_factor_map
            R
            (@comm_ring_idempotent_image R e idempotent)
            S
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            h
            candidate))
        (@comm_ring_hom_apply
          R
          (@comm_ring_idempotent_image R e idempotent)
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          (@comm_ring_idempotent_image_element R e x))
        x
        (@comm_ring_idempotent_image_scale_retract R e idempotent x));

symbol comm_ring_idempotent_image_factor_map_path
  [R S : τ CommRing]
  [e : τ (@comm_ring_carrier R)]
  [idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)]
  [h : τ (@CommRingHom R S)]
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  (candidate : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h))
  : τ (@=
      (@CommRingHom
        (@comm_ring_idempotent_image R e idempotent) S)
      (@comm_ring_idempotent_image_factor_map
        R e idempotent S h unit)
      (@comm_ring_localization_factor_map
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h
        candidate))
≔ @comm_ring_hom_ext
    (@comm_ring_idempotent_image R e idempotent)
    S
    (@comm_ring_idempotent_image_factor_map R e idempotent S h unit)
    (@comm_ring_localization_factor_map
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h
      candidate)
    (@comm_ring_idempotent_image_competitor_pointwise
      R S e idempotent h unit candidate);

symbol comm_ring_idempotent_image_factor_path
  [R S : τ CommRing]
  [e : τ (@comm_ring_carrier R)]
  [idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e)]
  [h : τ (@CommRingHom R S)]
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  (candidate : τ (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h))
  : τ (@=
      (@CommRingLocalizationFactor
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h)
      (@comm_ring_idempotent_image_factor_center
        R e idempotent S h unit)
      candidate)
≔ @Struct_sigma
    (@=
      (@CommRingHom (@comm_ring_idempotent_image R e idempotent) S)
      (@comm_ring_idempotent_image_factor_map
        R e idempotent S h unit)
      (@comm_ring_localization_factor_map
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h
        candidate))
    (λ p : τ (@=
        (@CommRingHom (@comm_ring_idempotent_image R e idempotent) S)
        (@comm_ring_idempotent_image_factor_map
          R e idempotent S h unit)
        (@comm_ring_localization_factor_map
          R
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          h
          candidate)),
      @PathOver
        (@CommRingHom (@comm_ring_idempotent_image R e idempotent) S)
        (λ factor : τ (@CommRingHom
            (@comm_ring_idempotent_image R e idempotent) S),
          @CommRingLocalizationAgreement
            R
            (@comm_ring_idempotent_image R e idempotent)
            S
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            factor h)
        (@comm_ring_idempotent_image_factor_map
          R e idempotent S h unit)
        (@comm_ring_localization_factor_map
          R
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          h
          candidate)
        p
        (@comm_ring_idempotent_image_factor_agreement
          R e idempotent S h unit)
        (@comm_ring_localization_factor_agreement
          R
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          h
          candidate))
    (@comm_ring_idempotent_image_factor_map_path
      R S e idempotent h unit candidate)
    (@comm_ring_localization_agreement_pathover
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h
      (@comm_ring_idempotent_image_factor_map R e idempotent S h unit)
      (@comm_ring_localization_factor_map
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h
        candidate)
      (@comm_ring_idempotent_image_factor_agreement
        R e idempotent S h unit)
      (@comm_ring_localization_factor_agreement
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h
        candidate)
      (@comm_ring_idempotent_image_factor_map_path
        R S e idempotent h unit candidate));

symbol comm_ring_idempotent_image_factor_is_contr
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  (S : τ CommRing)
  (h : τ (@CommRingHom R S))
  (unit : τ (@CommRingUnitEvidence S
      (@comm_ring_hom_apply R S h e)))
  : τ (IsContr (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h))
≔ @Struct_sigma
    (@CommRingLocalizationFactor
      R
      (@comm_ring_idempotent_image R e idempotent)
      S
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      h)
    (λ centre : τ (@CommRingLocalizationFactor
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h),
      @Pi_grpd
        (@CommRingLocalizationFactor
          R
          (@comm_ring_idempotent_image R e idempotent)
          S
          (@comm_ring_idempotent_image_localization_map R e idempotent)
          h)
        (λ candidate : τ (@CommRingLocalizationFactor
            R
            (@comm_ring_idempotent_image R e idempotent)
            S
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            h),
          @= (@CommRingLocalizationFactor
            R
            (@comm_ring_idempotent_image R e idempotent)
            S
            (@comm_ring_idempotent_image_localization_map R e idempotent)
            h)
            centre candidate))
    (@comm_ring_idempotent_image_factor_center
      R e idempotent S h unit)
    (λ candidate : τ (@CommRingLocalizationFactor
        R
        (@comm_ring_idempotent_image R e idempotent)
        S
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        h),
      @comm_ring_idempotent_image_factor_path
        R S e idempotent h unit candidate);

symbol comm_ring_idempotent_image_inverted_unit
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingUnitEvidence
      (@comm_ring_idempotent_image R e idempotent)
      (@comm_ring_hom_apply
        R
        (@comm_ring_idempotent_image R e idempotent)
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        e))
≔ @comm_ring_unit_transport_forward
    (@comm_ring_idempotent_image R e idempotent)
    (@comm_ring_one (@comm_ring_idempotent_image R e idempotent))
    (@comm_ring_hom_apply
      R
      (@comm_ring_idempotent_image R e idempotent)
      (@comm_ring_idempotent_image_localization_map R e idempotent)
      e)
    (@eq_sym
      (@comm_ring_carrier
        (@comm_ring_idempotent_image R e idempotent))
      (@comm_ring_hom_apply
        R
        (@comm_ring_idempotent_image R e idempotent)
        (@comm_ring_idempotent_image_localization_map R e idempotent)
        e)
      (@comm_ring_one (@comm_ring_idempotent_image R e idempotent))
      (@comm_ring_idempotent_image_localization_e_is_one
        R e idempotent))
    (@comm_ring_one_unit (@comm_ring_idempotent_image R e idempotent));

symbol comm_ring_idempotent_image_is_localization
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@IsCommRingLocalizationAt
      R e
      (@comm_ring_idempotent_image R e idempotent)
      (@comm_ring_idempotent_image_localization_map R e idempotent))
≔ @comm_ring_localization_property_intro
    R e
    (@comm_ring_idempotent_image R e idempotent)
    (@comm_ring_idempotent_image_localization_map R e idempotent)
    (@comm_ring_idempotent_image_inverted_unit R e idempotent)
    (λ S : τ CommRing,
      λ h : τ (@CommRingHom R S),
        λ unit : τ (@CommRingUnitEvidence S
            (@comm_ring_hom_apply R S h e)),
          @comm_ring_idempotent_image_factor_is_contr
            R e idempotent S h unit);

// Selected concrete localization R[1/e] = {x : R | e*x=x} for e^2=e.
symbol comm_ring_idempotent_image_localization
  (R : τ CommRing)
  (e : τ (@comm_ring_carrier R))
  (idempotent : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R e e) e))
  : τ (@CommRingLocalizationAt R e)
≔ @comm_ring_localization_intro
    R e
    (@comm_ring_idempotent_image R e idempotent)
    (@comm_ring_idempotent_image_localization_map R e idempotent)
    (@comm_ring_idempotent_image_is_localization R e idempotent);
