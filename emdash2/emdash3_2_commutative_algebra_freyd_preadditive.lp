/*
  Preadditive structure on the formal Freyd presentation category.

  Each quotient Hom receives the checked set-valued abelian-group structure.
  The semantic bilinearity paths use `comm_ring_freyd_comp`; the generic
  preadditive package is stated with ordinary categorical `comp_fapp0`.
  Explicit usability paths connect those presentations on the outer composite
  and on both resulting summands. No generic composition rewrite is added.

  This module claims preadditivity only. Zero objects, biproducts, additive
  structure, weak kernels, and Abelian structure remain separate layers.
*/

require open emdash.emdash3_2_preadditive_categories;
require open emdash.emdash3_2_commutative_algebra_freyd_preadditive_laws;

// Selected abelian-group operations on one quotient Hom.
symbol comm_ring_freyd_abelian_group_ops
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@AbelianGroupOps
      (Hom (@CommRingFreydPresentation_cat R) P Q))
≔ @abelian_group_ops_intro
    (Hom (@CommRingFreydPresentation_cat R) P Q)
    (@comm_ring_freyd_zero_class R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        @comm_ring_freyd_add R P Q f g)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_neg R P Q f);

// Full abelian-group laws on arbitrary quotient-Hom points.
symbol comm_ring_freyd_abelian_group_laws
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@IsAbelianGroup
      (Hom (@CommRingFreydPresentation_cat R) P Q)
      (@comm_ring_freyd_abelian_group_ops R P Q))
≔ @abelian_group_laws_intro
    (Hom (@CommRingFreydPresentation_cat R) P Q)
    (@comm_ring_freyd_abelian_group_ops R P Q)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        λ h : τ (@CommRingFreydHomSet R P Q),
          @comm_ring_freyd_add_assoc_path R P Q f g h)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      λ g : τ (@CommRingFreydHomSet R P Q),
        @comm_ring_freyd_add_comm_path R P Q f g)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_add_zero_right_path R P Q f)
    (λ f : τ (@CommRingFreydHomSet R P Q),
      @comm_ring_freyd_add_inv_path R P Q f);

// Set-valued abelian-group structure on one quotient Hom.
symbol comm_ring_freyd_abelian_group_structure
  (R : τ CommRing)
  (P Q : τ (@CommRingPresentation R))
  : τ (@AbelianGroupStructure
      (Hom (@CommRingFreydPresentation_cat R) P Q))
≔ @abelian_group_structure_intro
    (Hom (@CommRingFreydPresentation_cat R) P Q)
    (@comm_ring_freyd_hom_set_is_set R P Q)
    (@comm_ring_freyd_abelian_group_ops R P Q)
    (@comm_ring_freyd_abelian_group_laws R P Q);

// The whole Hom-indexed family of abelian-group structures.
symbol comm_ring_freyd_preadditive_hom_structures
  (R : τ CommRing)
  : τ (@PreadditiveHomStructures
      (@CommRingFreydPresentation_cat R))
≔ λ P : τ (@CommRingPresentation R),
    λ Q : τ (@CommRingPresentation R),
      @comm_ring_freyd_abelian_group_structure R P Q;

/*
  The sum of two semantic composites agrees with the sum of the two generic
  categorical composites. Each summand is reframed by the already-checked
  generic/semantic usability path; addition itself remains semantic.
*/
symbol comm_ring_freyd_add_semantic_comp_to_generic_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g h : τ (@CommRingFreydHomSet R Q S))
  (f k : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S g f)
        (@comm_ring_freyd_comp R P Q S h k))
      (@comm_ring_freyd_add R P S
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S g f)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h k)))
≔ @eq_trans
    (@CommRingFreydHomSet R P S)
    (@comm_ring_freyd_add R P S
      (@comm_ring_freyd_comp R P Q S g f)
      (@comm_ring_freyd_comp R P Q S h k))
    (@comm_ring_freyd_add R P S
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@comm_ring_freyd_comp R P Q S h k))
    (@comm_ring_freyd_add R P S
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h k))
    (@eq_ap
      (@CommRingFreydHomSet R P S)
      (@CommRingFreydHomSet R P S)
      (λ x : τ (@CommRingFreydHomSet R P S),
        @comm_ring_freyd_add R P S x
          (@comm_ring_freyd_comp R P Q S h k))
      (@comm_ring_freyd_comp R P Q S g f)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@eq_sym
        (@CommRingFreydHomSet R P S)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S g f)
        (@comm_ring_freyd_comp R P Q S g f)
        (@comm_ring_freyd_comp_usability_path R P Q S g f)))
    (@eq_ap
      (@CommRingFreydHomSet R P S)
      (@CommRingFreydHomSet R P S)
      (λ x : τ (@CommRingFreydHomSet R P S),
        @comm_ring_freyd_add R P S
          (@comp_fapp0
            (@CommRingFreydPresentation_cat R)
            P Q S g f)
          x)
      (@comm_ring_freyd_comp R P Q S h k)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h k)
      (@eq_sym
        (@CommRingFreydHomSet R P S)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h k)
        (@comm_ring_freyd_comp R P Q S h k)
        (@comm_ring_freyd_comp_usability_path R P Q S h k)));

// Generic categorical right distributivity, explicitly reframed through usability.
symbol comm_ring_freyd_generic_comp_add_right_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (h : τ (@CommRingFreydHomSet R Q S))
  (f g : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h
        (@comm_ring_freyd_add R P Q f g))
      (@comm_ring_freyd_add R P S
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h f)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h g)))
≔ @eq_trans
    (@CommRingFreydHomSet R P S)
    (@comp_fapp0
      (@CommRingFreydPresentation_cat R)
      P Q S h
      (@comm_ring_freyd_add R P Q f g))
    (@comm_ring_freyd_comp R P Q S h
      (@comm_ring_freyd_add R P Q f g))
    (@comm_ring_freyd_add R P S
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h f)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h g))
    (@comm_ring_freyd_comp_usability_path R P Q S h
      (@comm_ring_freyd_add R P Q f g))
    (@eq_trans
      (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S h
        (@comm_ring_freyd_add R P Q f g))
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S h f)
        (@comm_ring_freyd_comp R P Q S h g))
      (@comm_ring_freyd_add R P S
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h f)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h g))
      (@comm_ring_freyd_comp_add_right_path R P Q S h f g)
      (@comm_ring_freyd_add_semantic_comp_to_generic_path
        R P Q S h h f g));

// Generic categorical left distributivity, explicitly reframed through usability.
symbol comm_ring_freyd_generic_comp_add_left_path
  [R : τ CommRing]
  [P Q S : τ (@CommRingPresentation R)]
  (g h : τ (@CommRingFreydHomSet R Q S))
  (f : τ (@CommRingFreydHomSet R P Q))
  : τ (@= (@CommRingFreydHomSet R P S)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S
        (@comm_ring_freyd_add R Q S g h) f)
      (@comm_ring_freyd_add R P S
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S g f)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h f)))
≔ @eq_trans
    (@CommRingFreydHomSet R P S)
    (@comp_fapp0
      (@CommRingFreydPresentation_cat R)
      P Q S
      (@comm_ring_freyd_add R Q S g h) f)
    (@comm_ring_freyd_comp R P Q S
      (@comm_ring_freyd_add R Q S g h) f)
    (@comm_ring_freyd_add R P S
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S g f)
      (@comp_fapp0
        (@CommRingFreydPresentation_cat R)
        P Q S h f))
    (@comm_ring_freyd_comp_usability_path R P Q S
      (@comm_ring_freyd_add R Q S g h) f)
    (@eq_trans
      (@CommRingFreydHomSet R P S)
      (@comm_ring_freyd_comp R P Q S
        (@comm_ring_freyd_add R Q S g h) f)
      (@comm_ring_freyd_add R P S
        (@comm_ring_freyd_comp R P Q S g f)
        (@comm_ring_freyd_comp R P Q S h f))
      (@comm_ring_freyd_add R P S
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S g f)
        (@comp_fapp0
          (@CommRingFreydPresentation_cat R)
          P Q S h f))
      (@comm_ring_freyd_comp_add_left_path R P Q S g h f)
      (@comm_ring_freyd_add_semantic_comp_to_generic_path
        R P Q S g h f f));

// Both generic categorical bilinearity orientations.
symbol comm_ring_freyd_preadditive_bilinear
  (R : τ CommRing)
  : τ (@PreadditiveCompositionBilinear
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive_hom_structures R))
≔ @Product_pair_grpd _ _
    (λ P : τ (@CommRingPresentation R),
      λ Q : τ (@CommRingPresentation R),
        λ S : τ (@CommRingPresentation R),
          λ h : τ (@CommRingFreydHomSet R Q S),
            λ f : τ (@CommRingFreydHomSet R P Q),
              λ g : τ (@CommRingFreydHomSet R P Q),
                @comm_ring_freyd_generic_comp_add_right_path
                  R P Q S h f g)
    (λ P : τ (@CommRingPresentation R),
      λ Q : τ (@CommRingPresentation R),
        λ S : τ (@CommRingPresentation R),
          λ g : τ (@CommRingFreydHomSet R Q S),
            λ h : τ (@CommRingFreydHomSet R Q S),
              λ f : τ (@CommRingFreydHomSet R P Q),
                @comm_ring_freyd_generic_comp_add_left_path
                  R P Q S g h f);

// First honest preadditive-category instance for the formal Freyd category.
symbol comm_ring_freyd_preadditive
  (R : τ CommRing)
  : τ (@PreadditiveCategory (@CommRingFreydPresentation_cat R))
≔ @preadditive_category_intro
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive_hom_structures R)
    (@comm_ring_freyd_preadditive_bilinear R);
