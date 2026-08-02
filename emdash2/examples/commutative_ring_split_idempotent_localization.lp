/*
  Reviewer for componentwise product rings, F2, and split-idempotent affine
  restriction.  It checks object computation, structured map action and whole
  identity evidence, the closed ring model, non-endpoint idempotence, and the
  computing affine map (x,y) |-> (x,0).
*/

require open emdash.emdash3_2_commutative_algebra_localization_split;

assert (R S : τ CommRing) ⊢
  @comm_ring_product R S : τ CommRing;

assert (R S : τ CommRing) ⊢
  @comm_ring_carrier (@comm_ring_product R S)
  ≡ @Product_grpd (@comm_ring_carrier R) (@comm_ring_carrier S);

assert (R S : τ CommRing) ⊢
  @comm_ring_zero (@comm_ring_product R S)
  ≡ @Product_pair_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_zero R)
      (@comm_ring_zero S);

assert (R S : τ CommRing)
  (x y : τ (@comm_ring_carrier (@comm_ring_product R S))) ⊢
  @comm_ring_mul (@comm_ring_product R S) x y
  ≡ @Product_pair_grpd
      (@comm_ring_carrier R)
      (@comm_ring_carrier S)
      (@comm_ring_mul R (sigma_Fst x) (sigma_Fst y))
      (@comm_ring_mul S (sigma_Snd x) (sigma_Snd y));

assert (R R' S S' : τ CommRing)
  (h : τ (@CommRingHom R R'))
  (k : τ (@CommRingHom S S'))
  (x : τ (@comm_ring_carrier (@comm_ring_product R S))) ⊢
  @comm_ring_hom_apply
    (@comm_ring_product R S)
    (@comm_ring_product R' S')
    (@comm_ring_product_map R R' S S' h k)
    x
  ≡ @Product_pair_grpd
      (@comm_ring_carrier R')
      (@comm_ring_carrier S')
      (@comm_ring_hom_apply R R' h (sigma_Fst x))
      (@comm_ring_hom_apply S S' k (sigma_Snd x));

assert (R S : τ CommRing) ⊢
  @comm_ring_product_map_identity_path R S
  : τ (@=
      (@CommRingHom
        (@comm_ring_product R S)
        (@comm_ring_product R S))
      (@comm_ring_product_map
        R R S S
        (@comm_ring_hom_id_pointwise R)
        (@comm_ring_hom_id_pointwise S))
      (@comm_ring_hom_id_pointwise (@comm_ring_product R S)));

assert (R0 R1 R2 S0 S1 S2 : τ CommRing)
  (gR : τ (@CommRingHom R1 R2))
  (fR : τ (@CommRingHom R0 R1))
  (gS : τ (@CommRingHom S1 S2))
  (fS : τ (@CommRingHom S0 S1)) ⊢
  @comm_ring_product_map_comp_path
    R0 R1 R2 S0 S1 S2 gR fR gS fS
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
        (@comm_ring_product_map R0 R1 S0 S1 fR fS)));


assert ⊢ @comm_ring_carrier f2_comm_ring ≡ Bool_grpd;

assert ⊢ @comm_ring_zero f2_comm_ring ≡ false;

assert ⊢ @comm_ring_one f2_comm_ring ≡ true;

assert (x : τ Bool_grpd) ⊢ @comm_ring_mul f2_comm_ring true x ≡ x;

assert (x : τ Bool_grpd) ⊢ @comm_ring_mul f2_comm_ring false x ≡ false;


assert ⊢ f2_split_idempotent_path
  : τ (@=
      (@comm_ring_carrier f2_split_comm_ring)
      (@comm_ring_mul
        f2_split_comm_ring
        f2_split_idempotent
        f2_split_idempotent)
      f2_split_idempotent);

assert ⊢ f2_split_idempotent_not_zero
  : τ (@Function_grpd
      (@= (@comm_ring_carrier f2_split_comm_ring)
        f2_split_idempotent
        (@comm_ring_zero f2_split_comm_ring))
      Empty_grpd);

assert ⊢ f2_split_idempotent_not_one
  : τ (@Function_grpd
      (@= (@comm_ring_carrier f2_split_comm_ring)
        f2_split_idempotent
        (@comm_ring_one f2_split_comm_ring))
      Empty_grpd);

assert ⊢ sigma_Fst f2_split_basic_open_arrow
  ≡ @comm_ring_idempotent_image
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_path;

assert ⊢ sigma_Snd f2_split_basic_open_arrow
  ≡ @comm_ring_idempotent_image_localization_map
      f2_split_comm_ring
      f2_split_idempotent
      f2_split_idempotent_path;

assert (R S : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  (y : τ (@comm_ring_carrier S)) ⊢
  @comm_ring_product_split_scale_path R S x y
  : τ (@=
      (@comm_ring_carrier (@comm_ring_product R S))
      (@comm_ring_idempotent_image_element
        (@comm_ring_product R S)
        (@comm_ring_product_split_idempotent R S)
        (@comm_ring_hom_apply
          (@comm_ring_product R S)
          (@comm_ring_idempotent_image
            (@comm_ring_product R S)
            (@comm_ring_product_split_idempotent R S)
            (@comm_ring_product_split_idempotent_path R S))
          (sigma_Snd (@comm_ring_product_split_basic_open_arrow R S))
          (@Product_pair_grpd
            (@comm_ring_carrier R)
            (@comm_ring_carrier S)
            x y)))
      (@Product_pair_grpd
        (@comm_ring_carrier R)
        (@comm_ring_carrier S)
        x
        (@comm_ring_zero S)));

// The affine restriction map (x,y) |-> (x,0) computes on open points.
assert (x y : τ Bool_grpd) ⊢
  @comm_ring_idempotent_image_element
    f2_split_comm_ring
    f2_split_idempotent
    (@comm_ring_hom_apply
      f2_split_comm_ring
      (@comm_ring_idempotent_image
        f2_split_comm_ring
        f2_split_idempotent
        f2_split_idempotent_path)
      (sigma_Snd f2_split_basic_open_arrow)
      (@Product_pair_grpd Bool_grpd Bool_grpd x y))
  ≡ @Product_pair_grpd Bool_grpd Bool_grpd x false;
