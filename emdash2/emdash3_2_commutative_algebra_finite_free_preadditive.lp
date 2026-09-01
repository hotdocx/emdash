/*
  Preadditive structure on the finite-free matrix category.

  Each column-matrix Hom receives its existing componentwise abelian-group
  operations and laws. Generic categorical composition remains the runtime
  owner; its named comparison with transparent matrix multiplication transports
  both distributivity orientations. No matrix or category operation is
  duplicated and no rewrite/unification rule is added.
*/

require open emdash.emdash3_2_preadditive_categories;
require open emdash.emdash3_2_commutative_algebra_finite_free_category;
require open emdash.emdash3_2_commutative_algebra_matrix_additive_laws;

symbol comm_ring_vector_is_set
  (R : τ CommRing)
  (n : τ Nat_grpd)
  : τ (IsSetGrpd (@CommRingVector R n))
≔ @finite_family_is_set
    (@comm_ring_carrier R)
    (@comm_ring_carrier_is_set R)
    n;

symbol comm_ring_matrix_is_set
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  : τ (IsSetGrpd (@CommRingMatrix R rows columns))
≔ @finite_family_is_set
    (@CommRingVector R rows)
    (@comm_ring_vector_is_set R rows)
    columns;

symbol comm_ring_finite_free_abelian_group_ops
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  : τ (@AbelianGroupOps
      (Hom (@CommRingFiniteFree_cat R) source target))
≔ @abelian_group_ops_intro
    (Hom (@CommRingFiniteFree_cat R) source target)
    (@comm_ring_matrix_zero R target source)
    (λ f : τ (@CommRingMatrix R target source),
      λ g : τ (@CommRingMatrix R target source),
        @comm_ring_matrix_add R target source f g)
    (λ f : τ (@CommRingMatrix R target source),
      @comm_ring_matrix_neg R target source f);

symbol comm_ring_finite_free_abelian_group_laws
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  : τ (@IsAbelianGroup
      (Hom (@CommRingFiniteFree_cat R) source target)
      (@comm_ring_finite_free_abelian_group_ops R source target))
≔ @abelian_group_laws_intro
    (Hom (@CommRingFiniteFree_cat R) source target)
    (@comm_ring_finite_free_abelian_group_ops R source target)
    (λ f : τ (@CommRingMatrix R target source),
      λ g : τ (@CommRingMatrix R target source),
        λ h : τ (@CommRingMatrix R target source),
          @comm_ring_matrix_add_assoc_path R target source f g h)
    (λ f : τ (@CommRingMatrix R target source),
      λ g : τ (@CommRingMatrix R target source),
        @comm_ring_matrix_add_comm_path R target source f g)
    (λ f : τ (@CommRingMatrix R target source),
      @comm_ring_matrix_add_zero_right_path R target source f)
    (λ f : τ (@CommRingMatrix R target source),
      @comm_ring_matrix_add_inv_path R target source f);

symbol comm_ring_finite_free_abelian_group_structure
  (R : τ CommRing)
  (source target : τ Nat_grpd)
  : τ (@AbelianGroupStructure
      (Hom (@CommRingFiniteFree_cat R) source target))
≔ @abelian_group_structure_intro
    (Hom (@CommRingFiniteFree_cat R) source target)
    (@comm_ring_matrix_is_set R target source)
    (@comm_ring_finite_free_abelian_group_ops R source target)
    (@comm_ring_finite_free_abelian_group_laws R source target);

symbol comm_ring_finite_free_preadditive_hom_structures
  (R : τ CommRing)
  : τ (@PreadditiveHomStructures (@CommRingFiniteFree_cat R))
≔ λ source : τ Nat_grpd, λ target : τ Nat_grpd,
    @comm_ring_finite_free_abelian_group_structure R source target;

// A sum of transparent composites reframes to generic categorical composites.
symbol comm_ring_finite_free_add_transparent_to_generic_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g h : τ (@CommRingMatrix R target middle))
  (f k : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comm_ring_matrix_add R target source
        (@comm_ring_matrix_comp R target middle source g f)
        (@comm_ring_matrix_comp R target middle source h k))
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target h k)))
≔ @comm_ring_matrix_add_congr_path R target source
    (@comm_ring_matrix_comp R target middle source g f)
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      source middle target g f)
    (@comm_ring_matrix_comp R target middle source h k)
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      source middle target h k)
    (@eq_sym
      (@CommRingMatrix R target source)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target g f)
      (@comm_ring_matrix_comp R target middle source g f)
      (@comm_ring_finite_free_comp_fapp0_transparent_path
        R source middle target g f))
    (@eq_sym
      (@CommRingMatrix R target source)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target h k)
      (@comm_ring_matrix_comp R target middle source h k)
      (@comm_ring_finite_free_comp_fapp0_transparent_path
        R source middle target h k));

symbol comm_ring_finite_free_generic_comp_add_right_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g : τ (@CommRingMatrix R target middle))
  (f h : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target g
        (@comm_ring_matrix_add R middle source f h))
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g h)))
≔ @eq_trans
    (@CommRingMatrix R target source)
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      source middle target g
      (@comm_ring_matrix_add R middle source f h))
    (@comm_ring_matrix_comp R target middle source g
      (@comm_ring_matrix_add R middle source f h))
    (@comm_ring_matrix_add R target source
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target g f)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target g h))
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      source middle target g
      (@comm_ring_matrix_add R middle source f h))
    (@eq_trans
      (@CommRingMatrix R target source)
      (@comm_ring_matrix_comp R target middle source g
        (@comm_ring_matrix_add R middle source f h))
      (@comm_ring_matrix_add R target source
        (@comm_ring_matrix_comp R target middle source g f)
        (@comm_ring_matrix_comp R target middle source g h))
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g h))
      (@comm_ring_matrix_comp_add_right_path R
        target middle source g f h)
      (@comm_ring_finite_free_add_transparent_to_generic_path R
        source middle target g g f h));

symbol comm_ring_finite_free_generic_comp_add_left_path
  (R : τ CommRing)
  (source middle target : τ Nat_grpd)
  (g h : τ (@CommRingMatrix R target middle))
  (f : τ (@CommRingMatrix R middle source))
  : τ (@= (@CommRingMatrix R target source)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target
        (@comm_ring_matrix_add R target middle g h) f)
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target h f)))
≔ @eq_trans
    (@CommRingMatrix R target source)
    (@comp_fapp0 (@CommRingFiniteFree_cat R)
      source middle target
      (@comm_ring_matrix_add R target middle g h) f)
    (@comm_ring_matrix_comp R target middle source
      (@comm_ring_matrix_add R target middle g h) f)
    (@comm_ring_matrix_add R target source
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target g f)
      (@comp_fapp0 (@CommRingFiniteFree_cat R)
        source middle target h f))
    (@comm_ring_finite_free_comp_fapp0_transparent_path R
      source middle target
      (@comm_ring_matrix_add R target middle g h) f)
    (@eq_trans
      (@CommRingMatrix R target source)
      (@comm_ring_matrix_comp R target middle source
        (@comm_ring_matrix_add R target middle g h) f)
      (@comm_ring_matrix_add R target source
        (@comm_ring_matrix_comp R target middle source g f)
        (@comm_ring_matrix_comp R target middle source h f))
      (@comm_ring_matrix_add R target source
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target g f)
        (@comp_fapp0 (@CommRingFiniteFree_cat R)
          source middle target h f))
      (@comm_ring_matrix_comp_add_left_path R
        target middle source g h f)
      (@comm_ring_finite_free_add_transparent_to_generic_path R
        source middle target g h f f));

symbol comm_ring_finite_free_preadditive_bilinear
  (R : τ CommRing)
  : τ (@PreadditiveCompositionBilinear
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_preadditive_hom_structures R))
≔ @Product_pair_grpd _ _
    (λ source : τ Nat_grpd,
      λ middle : τ Nat_grpd,
        λ target : τ Nat_grpd,
          λ g : τ (@CommRingMatrix R target middle),
            λ f : τ (@CommRingMatrix R middle source),
              λ h : τ (@CommRingMatrix R middle source),
                @comm_ring_finite_free_generic_comp_add_right_path
                  R source middle target g f h)
    (λ source : τ Nat_grpd,
      λ middle : τ Nat_grpd,
        λ target : τ Nat_grpd,
          λ g : τ (@CommRingMatrix R target middle),
            λ h : τ (@CommRingMatrix R target middle),
              λ f : τ (@CommRingMatrix R middle source),
                @comm_ring_finite_free_generic_comp_add_left_path
                  R source middle target g h f);

symbol comm_ring_finite_free_preadditive
  (R : τ CommRing)
  : τ (@PreadditiveCategory (@CommRingFiniteFree_cat R))
≔ @preadditive_category_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive_hom_structures R)
    (@comm_ring_finite_free_preadditive_bilinear R);
