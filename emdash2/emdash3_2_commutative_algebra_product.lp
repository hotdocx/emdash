/*
  Componentwise products of set-carrier commutative rings.

  The product carrier retains the stable Product path owner while its sethood
  is transported from the equivalent constant-family Sigma.  Operations and
  laws compute componentwise.  Structured maps act componentwise as well, and
  whole map paths establish identity and composition.

  This rule-free module deliberately does not introduce a primitive binary
  product functor head: the object and arrow actions are present, while a
  first-class functor facade remains consumer-gated.  It declares no
  localization, presheaf, topology, Spec, or scheme interface.
*/

require open emdash.emdash3_2_commutative_algebra_category;

// Component paths assemble to a path between product pairs.
symbol comm_ring_product_pair_path
  [A B : Grpd]
  [x x' : τ A]
  [y y' : τ B]
  (px : τ (@= A x x'))
  (py : τ (@= B y y'))
  : τ (@=
      (Product_grpd A B)
      (@Product_pair_grpd A B x y)
      (@Product_pair_grpd A B x' y'))
≔ @product_path_intro
    A B
    (@Product_pair_grpd A B x y)
    (@Product_pair_grpd A B x' y')
    px
    (@const_pathover A B x x' y y' px py);

// Every stable product point is propositionally its pair of projections.
symbol comm_ring_product_eta_path
  [A B : Grpd]
  (x : τ (@Product_grpd A B))
  : τ (@=
      (@Product_grpd A B)
      (@Product_pair_grpd A B (sigma_Fst x) (sigma_Snd x))
      x)
≔ @sigma_ind
    A
    (λ _ : τ A, B)
    (λ p : @τΣ_ A (λ _ : τ A, B),
      @= (@Product_grpd A B)
        (@Product_pair_grpd A B (sigma_Fst p) (sigma_Snd p))
        p)
    (λ a : τ A,
      λ b : τ B,
        @eq_refl
          (@Product_grpd A B)
          (@Product_pair_grpd A B a b))
    x;

// The public product carrier retains the stable Product path owner.
symbol CommRingProductCarrier
  (R S : τ CommRing)
  : Grpd
≔ @Product_grpd (@comm_ring_carrier R) (@comm_ring_carrier S);

// The stable Product classifier and its constant-family Sigma decoding have
// literally the same carrier.  Retain the Product path owner while moving
// truncation evidence across an explicit identity-on-elements equivalence.
// The equivalence below is used only for that truncation transport.
protected symbol comm_ring_product_sigma_equiv_by_inverse
  (A B : Grpd)
  : τ (@EquivByInverse
      (@Σ_ A (λ _ : τ A, B))
      (@Product_grpd A B)
      (λ x : τ (@Σ_ A (λ _ : τ A, B)), x)
      (λ x : τ (@Product_grpd A B), x))
≔ @Product_pair_grpd
    (@Pi_grpd
      (@Σ_ A (λ _ : τ A, B))
      (λ x : τ (@Σ_ A (λ _ : τ A, B)),
        @= (@Σ_ A (λ _ : τ A, B)) x x))
    (@Pi_grpd
      (@Product_grpd A B)
      (λ x : τ (@Product_grpd A B),
        @= (@Product_grpd A B) x x))
    (λ x : τ (@Σ_ A (λ _ : τ A, B)),
      @eq_refl (@Σ_ A (λ _ : τ A, B)) x)
    (λ x : τ (@Product_grpd A B),
      @eq_refl (@Product_grpd A B) x);

protected symbol comm_ring_product_sigma_type_equiv
  (A B : Grpd)
  : τ (TypeEquiv
      (@Σ_ A (λ _ : τ A, B))
      (@Product_grpd A B))
≔ @Struct_sigma
    (@Function_grpd
      (@Σ_ A (λ _ : τ A, B))
      (@Product_grpd A B))
    (λ f : τ (@Function_grpd
        (@Σ_ A (λ _ : τ A, B))
        (@Product_grpd A B)),
      @IsEquivMap
        (@Σ_ A (λ _ : τ A, B))
        (@Product_grpd A B)
        f)
    (λ x : τ (@Σ_ A (λ _ : τ A, B)), x)
    (@is_equiv_map_by_inverse
      (@Σ_ A (λ _ : τ A, B))
      (@Product_grpd A B)
      (λ x : τ (@Σ_ A (λ _ : τ A, B)), x)
      (λ x : τ (@Product_grpd A B), x)
      (@comm_ring_product_sigma_equiv_by_inverse A B));

symbol comm_ring_product_carrier_is_set
  (R S : τ CommRing)
  : τ (IsSetGrpd (@CommRingProductCarrier R S))
≔ @is_trunc_grpd_equiv_to
    trunc_zero
    (@Σ_
      (@comm_ring_carrier R)
      (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier S))
    (@CommRingProductCarrier R S)
    (@comm_ring_product_sigma_type_equiv
      (@comm_ring_carrier R)
      (@comm_ring_carrier S))
    (@is_trunc_sigma
      trunc_zero
      (@comm_ring_carrier R)
      (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier S)
      (@comm_ring_carrier_is_set R)
      (λ _ : τ (@comm_ring_carrier R), @comm_ring_carrier_is_set S));

// Zero and one are paired componentwise.
symbol comm_ring_product_zero
  (R S : τ CommRing)
  : τ (@CommRingProductCarrier R S)
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_zero R)
    (@comm_ring_zero S);

symbol comm_ring_product_one
  (R S : τ CommRing)
  : τ (@CommRingProductCarrier R S)
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_one R)
    (@comm_ring_one S);

// Addition, negation, and multiplication compute componentwise.
symbol comm_ring_product_add
  (R S : τ CommRing)
  (x y : τ (@CommRingProductCarrier R S))
  : τ (@CommRingProductCarrier R S)
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_add R (sigma_Fst x) (sigma_Fst y))
    (@comm_ring_add S (sigma_Snd x) (sigma_Snd y));

symbol comm_ring_product_neg
  (R S : τ CommRing)
  (x : τ (@CommRingProductCarrier R S))
  : τ (@CommRingProductCarrier R S)
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_neg R (sigma_Fst x))
    (@comm_ring_neg S (sigma_Snd x));

symbol comm_ring_product_mul
  (R S : τ CommRing)
  (x y : τ (@CommRingProductCarrier R S))
  : τ (@CommRingProductCarrier R S)
≔ @Product_pair_grpd
    (@comm_ring_carrier R)
    (@comm_ring_carrier S)
    (@comm_ring_mul R (sigma_Fst x) (sigma_Fst y))
    (@comm_ring_mul S (sigma_Snd x) (sigma_Snd y));

symbol comm_ring_product_set_package
  (R S : τ CommRing)
  : τ SetU_grpd
≔ @Struct_trunc_grpd
    trunc_zero
    (@CommRingProductCarrier R S)
    (@comm_ring_product_carrier_is_set R S);

symbol comm_ring_product_ops
  (R S : τ CommRing)
  : τ (@CommRingOps (@CommRingProductCarrier R S))
≔ @comm_ring_ops_intro
    (@CommRingProductCarrier R S)
    (@comm_ring_product_zero R S)
    (@comm_ring_product_one R S)
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        @comm_ring_product_add R S x y)
    (λ x : τ (@CommRingProductCarrier R S),
      @comm_ring_product_neg R S x)
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        @comm_ring_product_mul R S x y);

// Ring laws are assembled exclusively from the two component law packages.
symbol comm_ring_product_laws
  (R S : τ CommRing)
  : τ (@IsCommRing
      (@CommRingProductCarrier R S)
      (@comm_ring_product_ops R S))
≔ @comm_ring_laws_intro
    (@CommRingProductCarrier R S)
    (@comm_ring_product_ops R S)
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        λ z : τ (@CommRingProductCarrier R S),
          @comm_ring_product_pair_path
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            _ _ _ _
            ((@comm_ring_add_assoc_law R)
              (sigma_Fst x) (sigma_Fst y) (sigma_Fst z))
            ((@comm_ring_add_assoc_law S)
              (sigma_Snd x) (sigma_Snd y) (sigma_Snd z)))
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        @comm_ring_product_pair_path
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          _ _ _ _
          ((@comm_ring_add_comm_law R) (sigma_Fst x) (sigma_Fst y))
          ((@comm_ring_add_comm_law S) (sigma_Snd x) (sigma_Snd y)))
    (λ x : τ (@CommRingProductCarrier R S),
      @eq_trans
        (@CommRingProductCarrier R S)
        (@comm_ring_product_add R S x (@comm_ring_product_zero R S))
        (@Product_pair_grpd
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (sigma_Fst x)
          (sigma_Snd x))
        x
        (@comm_ring_product_pair_path
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          _ _ _ _
          ((@comm_ring_add_zero_law R) (sigma_Fst x))
          ((@comm_ring_add_zero_law S) (sigma_Snd x)))
        (@comm_ring_product_eta_path
          (@comm_ring_carrier R) (@comm_ring_carrier S) x))
    (λ x : τ (@CommRingProductCarrier R S),
      @comm_ring_product_pair_path
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        _ _ _ _
        ((@comm_ring_add_inv_law R) (sigma_Fst x))
        ((@comm_ring_add_inv_law S) (sigma_Snd x)))
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        λ z : τ (@CommRingProductCarrier R S),
          @comm_ring_product_pair_path
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            _ _ _ _
            ((@comm_ring_mul_assoc_law R)
              (sigma_Fst x) (sigma_Fst y) (sigma_Fst z))
            ((@comm_ring_mul_assoc_law S)
              (sigma_Snd x) (sigma_Snd y) (sigma_Snd z)))
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        @comm_ring_product_pair_path
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          _ _ _ _
          ((@comm_ring_mul_comm_law R) (sigma_Fst x) (sigma_Fst y))
          ((@comm_ring_mul_comm_law S) (sigma_Snd x) (sigma_Snd y)))
    (λ x : τ (@CommRingProductCarrier R S),
      @eq_trans
        (@CommRingProductCarrier R S)
        (@comm_ring_product_mul R S x (@comm_ring_product_one R S))
        (@Product_pair_grpd
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          (sigma_Fst x)
          (sigma_Snd x))
        x
        (@comm_ring_product_pair_path
          (@comm_ring_carrier R)
          (@comm_ring_carrier S)
          _ _ _ _
          ((@comm_ring_mul_one_law R) (sigma_Fst x))
          ((@comm_ring_mul_one_law S) (sigma_Snd x)))
        (@comm_ring_product_eta_path
          (@comm_ring_carrier R) (@comm_ring_carrier S) x))
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        λ z : τ (@CommRingProductCarrier R S),
          @comm_ring_product_pair_path
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            _ _ _ _
            ((@comm_ring_left_distrib_law R)
              (sigma_Fst x) (sigma_Fst y) (sigma_Fst z))
            ((@comm_ring_left_distrib_law S)
              (sigma_Snd x) (sigma_Snd y) (sigma_Snd z)));

symbol comm_ring_product_structure
  (R S : τ CommRing)
  : τ (@CommRingStructure (@CommRingProductCarrier R S))
≔ @comm_ring_structure_intro
    (@CommRingProductCarrier R S)
    (@comm_ring_product_ops R S)
    (@comm_ring_product_laws R S);

// The complete set-carrier commutative-ring product.
symbol comm_ring_product
  (R S : τ CommRing)
  : τ CommRing
≔ @comm_ring_intro
    (@comm_ring_product_set_package R S)
    (@comm_ring_product_structure R S);

/*
  Componentwise arrow action.  This is the reusable semantic content needed
  before a consumer justifies a primitive Functor head and projection rules.
  Identity and composition are proved as whole structured-map paths below.
*/
symbol comm_ring_product_map_laws
  [R R' S S' : τ CommRing]
  (h : τ (@CommRingHom R R'))
  (k : τ (@CommRingHom S S'))
  : τ (@CommRingHomLaws
      (@comm_ring_product R S)
      (@comm_ring_product R' S')
      (λ x : τ (@CommRingProductCarrier R S),
        @Product_pair_grpd
          (@comm_ring_carrier R')
          (@comm_ring_carrier S')
          (@comm_ring_hom_apply R R' h (sigma_Fst x))
          (@comm_ring_hom_apply S S' k (sigma_Snd x))))
≔ @comm_ring_hom_laws_intro
    (@comm_ring_product R S)
    (@comm_ring_product R' S')
    (λ x : τ (@CommRingProductCarrier R S),
      @Product_pair_grpd
        (@comm_ring_carrier R')
        (@comm_ring_carrier S')
        (@comm_ring_hom_apply R R' h (sigma_Fst x))
        (@comm_ring_hom_apply S S' k (sigma_Snd x)))
    (@comm_ring_product_pair_path
      (@comm_ring_carrier R')
      (@comm_ring_carrier S')
      _ _ _ _
      (@comm_ring_hom_zero_law R R' h)
      (@comm_ring_hom_zero_law S S' k))
    (@comm_ring_product_pair_path
      (@comm_ring_carrier R')
      (@comm_ring_carrier S')
      _ _ _ _
      (@comm_ring_hom_one_law R R' h)
      (@comm_ring_hom_one_law S S' k))
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        @comm_ring_product_pair_path
          (@comm_ring_carrier R')
          (@comm_ring_carrier S')
          _ _ _ _
          ((@comm_ring_hom_add_law R R' h) (sigma_Fst x) (sigma_Fst y))
          ((@comm_ring_hom_add_law S S' k) (sigma_Snd x) (sigma_Snd y)))
    (λ x : τ (@CommRingProductCarrier R S),
      @comm_ring_product_pair_path
        (@comm_ring_carrier R')
        (@comm_ring_carrier S')
        _ _ _ _
        ((@comm_ring_hom_neg_law R R' h) (sigma_Fst x))
        ((@comm_ring_hom_neg_law S S' k) (sigma_Snd x)))
    (λ x : τ (@CommRingProductCarrier R S),
      λ y : τ (@CommRingProductCarrier R S),
        @comm_ring_product_pair_path
          (@comm_ring_carrier R')
          (@comm_ring_carrier S')
          _ _ _ _
          ((@comm_ring_hom_mul_law R R' h) (sigma_Fst x) (sigma_Fst y))
          ((@comm_ring_hom_mul_law S S' k) (sigma_Snd x) (sigma_Snd y)));

symbol comm_ring_product_map
  [R R' S S' : τ CommRing]
  (h : τ (@CommRingHom R R'))
  (k : τ (@CommRingHom S S'))
  : τ (@CommRingHom
      (@comm_ring_product R S)
      (@comm_ring_product R' S'))
≔ @comm_ring_hom_intro
    (@comm_ring_product R S)
    (@comm_ring_product R' S')
    (λ x : τ (@CommRingProductCarrier R S),
      @Product_pair_grpd
        (@comm_ring_carrier R')
        (@comm_ring_carrier S')
        (@comm_ring_hom_apply R R' h (sigma_Fst x))
        (@comm_ring_hom_apply S S' k (sigma_Snd x)))
    (@comm_ring_product_map_laws R R' S S' h k);

symbol comm_ring_product_map_identity_pointwise_path
  (R S : τ CommRing)
  : τ (@CommRingHomPointwisePath
      (@comm_ring_product R S)
      (@comm_ring_product R S)
      (@comm_ring_product_map
        R R S S
        (@comm_ring_hom_id_pointwise R)
        (@comm_ring_hom_id_pointwise S))
      (@comm_ring_hom_id_pointwise (@comm_ring_product R S)))
≔ λ x : τ (@CommRingProductCarrier R S),
    @comm_ring_product_eta_path
      (@comm_ring_carrier R) (@comm_ring_carrier S) x;

symbol comm_ring_product_map_identity_path
  (R S : τ CommRing)
  : τ (@=
      (@CommRingHom
        (@comm_ring_product R S)
        (@comm_ring_product R S))
      (@comm_ring_product_map
        R R S S
        (@comm_ring_hom_id_pointwise R)
        (@comm_ring_hom_id_pointwise S))
      (@comm_ring_hom_id_pointwise (@comm_ring_product R S)))
≔ @comm_ring_hom_ext
    (@comm_ring_product R S)
    (@comm_ring_product R S)
    (@comm_ring_product_map
      R R S S
      (@comm_ring_hom_id_pointwise R)
      (@comm_ring_hom_id_pointwise S))
    (@comm_ring_hom_id_pointwise (@comm_ring_product R S))
    (@comm_ring_product_map_identity_pointwise_path R S);

symbol comm_ring_product_map_comp_pointwise_path
  [R0 R1 R2 S0 S1 S2 : τ CommRing]
  (gR : τ (@CommRingHom R1 R2))
  (fR : τ (@CommRingHom R0 R1))
  (gS : τ (@CommRingHom S1 S2))
  (fS : τ (@CommRingHom S0 S1))
  : τ (@CommRingHomPointwisePath
      (@comm_ring_product R0 S0)
      (@comm_ring_product R2 S2)
      (@comm_ring_product_map
        R0 R2 S0 S2
        (@comm_ring_hom_comp_pointwise R0 R1 R2 gR fR)
        (@comm_ring_hom_comp_pointwise S0 S1 S2 gS fS))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_product R0 S0)
        (@comm_ring_product R1 S1)
        (@comm_ring_product R2 S2)
        (@comm_ring_product_map R1 R2 S1 S2 gR gS)
        (@comm_ring_product_map R0 R1 S0 S1 fR fS)))
≔ λ x : τ (@CommRingProductCarrier R0 S0),
    @comm_ring_product_pair_path
      (@comm_ring_carrier R2)
      (@comm_ring_carrier S2)
      _ _ _ _
      (@eq_refl
        (@comm_ring_carrier R2)
        (@comm_ring_hom_apply R1 R2 gR
          (@comm_ring_hom_apply R0 R1 fR (sigma_Fst x))))
      (@eq_refl
        (@comm_ring_carrier S2)
        (@comm_ring_hom_apply S1 S2 gS
          (@comm_ring_hom_apply S0 S1 fS (sigma_Snd x))));

symbol comm_ring_product_map_comp_path
  [R0 R1 R2 S0 S1 S2 : τ CommRing]
  (gR : τ (@CommRingHom R1 R2))
  (fR : τ (@CommRingHom R0 R1))
  (gS : τ (@CommRingHom S1 S2))
  (fS : τ (@CommRingHom S0 S1))
  : τ (@=
      (@CommRingHom
        (@comm_ring_product R0 S0)
        (@comm_ring_product R2 S2))
      (@comm_ring_product_map
        R0 R2 S0 S2
        (@comm_ring_hom_comp_pointwise R0 R1 R2 gR fR)
        (@comm_ring_hom_comp_pointwise S0 S1 S2 gS fS))
      (@comm_ring_hom_comp_pointwise
        (@comm_ring_product R0 S0)
        (@comm_ring_product R1 S1)
        (@comm_ring_product R2 S2)
        (@comm_ring_product_map R1 R2 S1 S2 gR gS)
        (@comm_ring_product_map R0 R1 S0 S1 fR fS)))
≔ @comm_ring_hom_ext
    (@comm_ring_product R0 S0)
    (@comm_ring_product R2 S2)
    (@comm_ring_product_map
      R0 R2 S0 S2
      (@comm_ring_hom_comp_pointwise R0 R1 R2 gR fR)
      (@comm_ring_hom_comp_pointwise S0 S1 S2 gS fS))
    (@comm_ring_hom_comp_pointwise
      (@comm_ring_product R0 S0)
      (@comm_ring_product R1 S1)
      (@comm_ring_product R2 S2)
      (@comm_ring_product_map R1 R2 S1 S2 gR gS)
      (@comm_ring_product_map R0 R1 S0 S1 fR fS))
    (@comm_ring_product_map_comp_pointwise_path
      R0 R1 R2 S0 S1 S2 gR fR gS fS);
