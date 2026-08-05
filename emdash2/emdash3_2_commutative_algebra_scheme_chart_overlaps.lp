/*
  Selected intersections of the two charts of a binary site-relative scheme.

  The intersection is a supplied binary product of the two chart objects in
  the conventional slice K/X.  Its whole product comparison derives both
  slice projections.  Applying the existing whole slice-domain functor gives
  the two base arrows, and the global structure presheaf then computes both
  restriction homomorphisms into the overlap ring.

  This transparent, rule-free consumer does not add overlap, transition, or
  cocycle data to `BinarySiteRelativeSchemePresentation`; those remain owned
  by the already-global object and ordinary functor composition.  It also
  does not construct the pullback, assert that every pair of charts admits
  one, identify either chart with affine line, or claim projective geometry.
*/

require open emdash.emdash3_2_finite_limits;
require open emdash.emdash3_2_commutative_algebra_site_relative_schemes;

// Selected actual intersection of the two chart arrows in the slice K/X.
symbol BinarySchemeChartOverlapPresentation
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : Grpd
≔ @BinaryProductPresentation
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart0 K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart1 K S));

// Constructor for a supplied slice product and its whole universal property.
symbol binary_scheme_chart_overlap_intro
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (Obj (@Slice_cat K
      (@binary_site_relative_scheme_whole_object K S))))
  (universal : τ (@IsBinaryProduct_comp
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart0 K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart1 K S))
      overlap))
  : τ (@BinarySchemeChartOverlapPresentation K S)
≔ @binary_product_intro
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart0 K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart1 K S))
    overlap universal;

// Selected overlap object in the conventional slice.
symbol binary_scheme_chart_overlap_restriction
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (Obj (@Slice_cat K
      (@binary_site_relative_scheme_whole_object K S)))
≔ sigma_Fst overlap;

// Retained whole slice-product universal comparison.
symbol binary_scheme_chart_overlap_universal
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (@IsBinaryProduct_comp
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart0 K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart1 K S))
      (sigma_Fst overlap))
≔ sigma_Snd overlap;

// Whole slice projection from the intersection to chart 0.
symbol binary_scheme_chart_overlap_to_chart0
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (Hom
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      (sigma_Fst overlap)
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart0 K S)))
≔ @selected_binary_product_projection0
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart0 K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart1 K S))
    overlap;

// Whole slice projection from the intersection to chart 1.
symbol binary_scheme_chart_overlap_to_chart1
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (Hom
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      (sigma_Fst overlap)
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart1 K S)))
≔ @selected_binary_product_projection1
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart0 K S))
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart1 K S))
    overlap;

// Domain of the overlap arrow, projected by the whole slice-domain functor.
symbol binary_scheme_chart_overlap_domain
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (Obj K)
≔ @fapp0
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    K
    (@slice_domain_func K
      (@binary_site_relative_scheme_whole_object K S))
    (sigma_Fst overlap);

// The same whole domain functor evaluates both slice projections in K.
symbol binary_scheme_chart_overlap_domain_to_chart0
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (Hom K
      (@binary_scheme_chart_overlap_domain K S overlap)
      (@fapp0
        (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
        K
        (@slice_domain_func K
          (@binary_site_relative_scheme_whole_object K S))
        (@reflective_comm_ringed_space_cover_chart_restriction
          K
          (@binary_site_relative_scheme_global_cover K S)
          (@binary_site_relative_scheme_chart0 K S))))
≔ @fapp1_fapp0
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    K
    (@slice_domain_func K
      (@binary_site_relative_scheme_whole_object K S))
    (sigma_Fst overlap)
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart0 K S))
    (@binary_scheme_chart_overlap_to_chart0 K S overlap);

symbol binary_scheme_chart_overlap_domain_to_chart1
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (Hom K
      (@binary_scheme_chart_overlap_domain K S overlap)
      (@fapp0
        (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
        K
        (@slice_domain_func K
          (@binary_site_relative_scheme_whole_object K S))
        (@reflective_comm_ringed_space_cover_chart_restriction
          K
          (@binary_site_relative_scheme_global_cover K S)
          (@binary_site_relative_scheme_chart1 K S))))
≔ @fapp1_fapp0
    (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
    K
    (@slice_domain_func K
      (@binary_site_relative_scheme_whole_object K S))
    (sigma_Fst overlap)
    (@reflective_comm_ringed_space_cover_chart_restriction
      K
      (@binary_site_relative_scheme_global_cover K S)
      (@binary_site_relative_scheme_chart1 K S))
    (@binary_scheme_chart_overlap_to_chart1 K S overlap);

// Global structure rings on the two selected chart domains and their overlap.
symbol binary_scheme_chart0_structure_ring
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ CommRing
≔ @comm_ring_psh_value
    K
    (@binary_site_relative_scheme_underlying_psh K S)
    (@fapp0
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      K
      (@slice_domain_func K
        (@binary_site_relative_scheme_whole_object K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart0 K S)));

symbol binary_scheme_chart1_structure_ring
  [K : Cat]
  (S : τ (@BinarySiteRelativeSchemePresentation K))
  : τ CommRing
≔ @comm_ring_psh_value
    K
    (@binary_site_relative_scheme_underlying_psh K S)
    (@fapp0
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      K
      (@slice_domain_func K
        (@binary_site_relative_scheme_whole_object K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart1 K S)));

symbol binary_scheme_chart_overlap_ring
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ CommRing
≔ @comm_ring_psh_value
    K
    (@binary_site_relative_scheme_underlying_psh K S)
    (@binary_scheme_chart_overlap_domain K S overlap);

// Existing presheaf action computes both restrictions into the overlap ring.
symbol binary_scheme_chart_overlap_restriction0
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (@CommRingHom
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap))
≔ @comm_ring_psh_restriction_hom
    K
    (@binary_site_relative_scheme_underlying_psh K S)
    (@binary_scheme_chart_overlap_domain K S overlap)
    (@fapp0
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      K
      (@slice_domain_func K
        (@binary_site_relative_scheme_whole_object K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart0 K S)))
    (@binary_scheme_chart_overlap_domain_to_chart0 K S overlap);

symbol binary_scheme_chart_overlap_restriction1
  [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S))
  : τ (@CommRingHom
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap))
≔ @comm_ring_psh_restriction_hom
    K
    (@binary_site_relative_scheme_underlying_psh K S)
    (@binary_scheme_chart_overlap_domain K S overlap)
    (@fapp0
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      K
      (@slice_domain_func K
        (@binary_site_relative_scheme_whole_object K S))
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart1 K S)))
    (@binary_scheme_chart_overlap_domain_to_chart1 K S overlap);
