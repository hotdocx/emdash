/*
  Set-carrier commutative-ring objects.

  This one-way standard-library module separates operation data from law
  evidence and packages the carrier through SetU_grpd.  It deliberately does
  not yet declare ring morphisms, CommRing_cat, localization, finite families,
  powers, or polynomial algebras.
*/

require open emdash.emdash3_2_nat_arithmetic;

// Five operations; the laws are retained separately in IsCommRing.
symbol CommRingOps
  (A : Grpd)
  : Grpd
≔ `Σ_ zero : τ A,
   `Σ_ one : τ A,
   `Σ_ add : τ (@Function_grpd A (@Function_grpd A A)),
   `Σ_ neg : τ (@Function_grpd A A),
       @Function_grpd A (@Function_grpd A A);

symbol comm_ring_ops_intro
  [A : Grpd]
  (zero one : τ A)
  (add : τ (@Function_grpd A (@Function_grpd A A)))
  (neg : τ (@Function_grpd A A))
  (mul : τ (@Function_grpd A (@Function_grpd A A)))
  : τ (@CommRingOps A)
≔ Struct_sigma zero
    (Struct_sigma one
      (Struct_sigma add
        (Struct_sigma neg mul)));

symbol comm_ring_ops_zero
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : τ A
≔ sigma_Fst ops;

symbol comm_ring_ops_one
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : τ A
≔ sigma_Fst (sigma_Snd ops);

symbol comm_ring_ops_add_function
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : τ (@Function_grpd A (@Function_grpd A A))
≔ sigma_Fst (sigma_Snd (sigma_Snd ops));

symbol comm_ring_ops_neg_function
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : τ (@Function_grpd A A)
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd ops)));

symbol comm_ring_ops_mul_function
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : τ (@Function_grpd A (@Function_grpd A A))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd ops)));

symbol comm_ring_ops_add
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  (x y : τ A)
  : τ A
≔ (@comm_ring_ops_add_function A ops) x y;

symbol comm_ring_ops_neg
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  (x : τ A)
  : τ A
≔ (@comm_ring_ops_neg_function A ops) x;

symbol comm_ring_ops_mul
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  (x y : τ A)
  : τ A
≔ (@comm_ring_ops_mul_function A ops) x y;

// Additive commutative-group laws, stored in a sufficient one-sided basis.
symbol CommRingAddAssoc
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @Pi_grpd A (λ z : τ A,
        @= A
          (@comm_ring_ops_add A ops
            (@comm_ring_ops_add A ops x y) z)
          (@comm_ring_ops_add A ops
            x (@comm_ring_ops_add A ops y z)))));

symbol CommRingAddComm
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @= A
        (@comm_ring_ops_add A ops x y)
        (@comm_ring_ops_add A ops y x)));

symbol CommRingAddZero
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @= A
      (@comm_ring_ops_add A ops x (@comm_ring_ops_zero A ops))
      x);

symbol CommRingAddInv
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @= A
      (@comm_ring_ops_add A ops x (@comm_ring_ops_neg A ops x))
      (@comm_ring_ops_zero A ops));

// Multiplicative commutative-monoid laws and one distributivity orientation.
symbol CommRingMulAssoc
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @Pi_grpd A (λ z : τ A,
        @= A
          (@comm_ring_ops_mul A ops
            (@comm_ring_ops_mul A ops x y) z)
          (@comm_ring_ops_mul A ops
            x (@comm_ring_ops_mul A ops y z)))));

symbol CommRingMulComm
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @= A
        (@comm_ring_ops_mul A ops x y)
        (@comm_ring_ops_mul A ops y x)));

symbol CommRingMulOne
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @= A
      (@comm_ring_ops_mul A ops x (@comm_ring_ops_one A ops))
      x);

symbol CommRingLeftDistrib
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Pi_grpd A (λ x : τ A,
    @Pi_grpd A (λ y : τ A,
      @Pi_grpd A (λ z : τ A,
        @= A
          (@comm_ring_ops_mul A ops
            x (@comm_ring_ops_add A ops y z))
          (@comm_ring_ops_add A ops
            (@comm_ring_ops_mul A ops x y)
            (@comm_ring_ops_mul A ops x z)))));

/*
  Sufficient commutative-ring law package.

  Additive commutativity derives the omitted left zero/inverse equations;
  multiplicative commutativity derives the omitted left unit and right
  distributivity equations.  Zero and one are not required to be distinct.
*/
symbol IsCommRing
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  : Grpd
≔ @Product_grpd
    (@CommRingAddAssoc A ops)
    (@Product_grpd
      (@CommRingAddComm A ops)
      (@Product_grpd
        (@CommRingAddZero A ops)
        (@Product_grpd
          (@CommRingAddInv A ops)
          (@Product_grpd
            (@CommRingMulAssoc A ops)
            (@Product_grpd
              (@CommRingMulComm A ops)
              (@Product_grpd
                (@CommRingMulOne A ops)
                (@CommRingLeftDistrib A ops)))))));

symbol comm_ring_laws_intro
  [A : Grpd]
  [ops : τ (@CommRingOps A)]
  (add_assoc : τ (@CommRingAddAssoc A ops))
  (add_comm : τ (@CommRingAddComm A ops))
  (add_zero : τ (@CommRingAddZero A ops))
  (add_inv : τ (@CommRingAddInv A ops))
  (mul_assoc : τ (@CommRingMulAssoc A ops))
  (mul_comm : τ (@CommRingMulComm A ops))
  (mul_one : τ (@CommRingMulOne A ops))
  (left_distrib : τ (@CommRingLeftDistrib A ops))
  : τ (@IsCommRing A ops)
≔ Struct_sigma add_assoc
    (Struct_sigma add_comm
      (Struct_sigma add_zero
        (Struct_sigma add_inv
          (Struct_sigma mul_assoc
            (Struct_sigma mul_comm
              (Struct_sigma mul_one left_distrib))))));

// Ring structure on one already-selected carrier.
symbol CommRingStructure
  (A : Grpd)
  : Grpd
≔ `Σ_ ops : τ (@CommRingOps A), @IsCommRing A ops;

symbol comm_ring_structure_intro
  [A : Grpd]
  (ops : τ (@CommRingOps A))
  (laws : τ (@IsCommRing A ops))
  : τ (@CommRingStructure A)
≔ @Struct_sigma
    (@CommRingOps A)
    (λ data : τ (@CommRingOps A), @IsCommRing A data)
    ops laws;

// A commutative ring retains a set-valued carrier and a structure on it.
symbol CommRing
  : Grpd
≔ `Σ_ A : τ SetU_grpd,
    @CommRingStructure (@trunc_grpd_carrier trunc_zero A);

symbol comm_ring_intro
  (A : τ SetU_grpd)
  (structure : τ (@CommRingStructure
      (@trunc_grpd_carrier trunc_zero A)))
  : τ CommRing
≔ @Struct_sigma
    SetU_grpd
    (λ X : τ SetU_grpd,
      @CommRingStructure (@trunc_grpd_carrier trunc_zero X))
    A structure;

symbol comm_ring_carrier_package
  (R : τ CommRing)
  : τ SetU_grpd
≔ sigma_Fst R;

symbol comm_ring_carrier
  (R : τ CommRing)
  : Grpd
≔ @trunc_grpd_carrier trunc_zero (@comm_ring_carrier_package R);

symbol comm_ring_carrier_is_set
  (R : τ CommRing)
  : τ (IsSetGrpd (@comm_ring_carrier R))
≔ @trunc_grpd_evidence trunc_zero (@comm_ring_carrier_package R);

symbol comm_ring_structure
  (R : τ CommRing)
  : τ (@CommRingStructure (@comm_ring_carrier R))
≔ sigma_Snd R;

symbol comm_ring_ops
  (R : τ CommRing)
  : τ (@CommRingOps (@comm_ring_carrier R))
≔ sigma_Fst (@comm_ring_structure R);

symbol comm_ring_laws
  (R : τ CommRing)
  : τ (@IsCommRing (@comm_ring_carrier R) (@comm_ring_ops R))
≔ sigma_Snd (@comm_ring_structure R);

// Readable projections of the eight retained law fields.
symbol comm_ring_add_assoc_law
  (R : τ CommRing)
  : τ (@CommRingAddAssoc
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst (@comm_ring_laws R);

symbol comm_ring_add_comm_law
  (R : τ CommRing)
  : τ (@CommRingAddComm
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst (sigma_Snd (@comm_ring_laws R));

symbol comm_ring_add_zero_law
  (R : τ CommRing)
  : τ (@CommRingAddZero
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst (sigma_Snd (sigma_Snd (@comm_ring_laws R)));

symbol comm_ring_add_inv_law
  (R : τ CommRing)
  : τ (@CommRingAddInv
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst
    (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_laws R))));

symbol comm_ring_mul_assoc_law
  (R : τ CommRing)
  : τ (@CommRingMulAssoc
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst
    (sigma_Snd
      (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_laws R)))));

symbol comm_ring_mul_comm_law
  (R : τ CommRing)
  : τ (@CommRingMulComm
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst
    (sigma_Snd
      (sigma_Snd
        (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_laws R))))));

symbol comm_ring_mul_one_law
  (R : τ CommRing)
  : τ (@CommRingMulOne
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Fst
    (sigma_Snd
      (sigma_Snd
        (sigma_Snd
          (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_laws R)))))));

symbol comm_ring_left_distrib_law
  (R : τ CommRing)
  : τ (@CommRingLeftDistrib
      (@comm_ring_carrier R)
      (@comm_ring_ops R))
≔ sigma_Snd
    (sigma_Snd
      (sigma_Snd
        (sigma_Snd
          (sigma_Snd (sigma_Snd (sigma_Snd (@comm_ring_laws R)))))));

// Element-level end-user observations.
symbol comm_ring_zero
  (R : τ CommRing)
  : τ (@comm_ring_carrier R)
≔ @comm_ring_ops_zero
    (@comm_ring_carrier R)
    (@comm_ring_ops R);

symbol comm_ring_one
  (R : τ CommRing)
  : τ (@comm_ring_carrier R)
≔ @comm_ring_ops_one
    (@comm_ring_carrier R)
    (@comm_ring_ops R);

symbol comm_ring_add
  (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  : τ (@comm_ring_carrier R)
≔ @comm_ring_ops_add
    (@comm_ring_carrier R)
    (@comm_ring_ops R)
    x y;

symbol comm_ring_neg
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@comm_ring_carrier R)
≔ @comm_ring_ops_neg
    (@comm_ring_carrier R)
    (@comm_ring_ops R)
    x;

symbol comm_ring_mul
  (R : τ CommRing)
  (x y : τ (@comm_ring_carrier R))
  : τ (@comm_ring_carrier R)
≔ @comm_ring_ops_mul
    (@comm_ring_carrier R)
    (@comm_ring_ops R)
    x y;

/*
  Concrete one-element zero ring.

  Open Unit variables do not eta-reduce to tt.  The additive-zero and
  multiplicative-one witnesses therefore use the existing contraction path.
*/
symbol unit_set_package
  : τ SetU_grpd
≔ @Struct_trunc_grpd
    trunc_zero
    Unit_grpd
    (@prop_is_trunc_succ trunc_minus_one Unit_grpd unit_is_prop);

symbol zero_comm_ring_ops
  : τ (@CommRingOps Unit_grpd)
≔ @comm_ring_ops_intro
    Unit_grpd
    tt tt
    (λ _ : τ Unit_grpd, λ _ : τ Unit_grpd, tt)
    (λ _ : τ Unit_grpd, tt)
    (λ _ : τ Unit_grpd, λ _ : τ Unit_grpd, tt);

symbol zero_comm_ring_laws
  : τ (@IsCommRing Unit_grpd zero_comm_ring_ops)
≔ @comm_ring_laws_intro
    Unit_grpd
    zero_comm_ring_ops
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt)
    (λ x : τ Unit_grpd, (sigma_Snd unit_is_contr) x)
    (λ _ : τ Unit_grpd, @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt)
    (λ x : τ Unit_grpd, (sigma_Snd unit_is_contr) x)
    (λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      λ _ : τ Unit_grpd,
      @eq_refl Unit_grpd tt);

symbol zero_comm_ring_structure
  : τ (@CommRingStructure Unit_grpd)
≔ @comm_ring_structure_intro
    Unit_grpd zero_comm_ring_ops zero_comm_ring_laws;

symbol zero_comm_ring
  : τ CommRing
≔ @comm_ring_intro unit_set_package zero_comm_ring_structure;
