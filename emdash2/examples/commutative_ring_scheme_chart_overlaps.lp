/*
  Reviewer for selected intersections of binary site-relative scheme charts.

  The overlap is an actual binary product in the conventional slice.  Its
  projections, underlying base arrows, overlap structure ring, and both ring
  restrictions are all derived through existing whole owners.  No gluing or
  external compatibility field is retained.
*/

require open emdash.emdash3_2_commutative_algebra_scheme_chart_overlaps;

// The supplied overlap object and its whole comparison have Sigma beta.
assert [K : Cat]
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
      overlap)) ⊢
  @binary_scheme_chart_overlap_restriction
    K S (@binary_scheme_chart_overlap_intro K S overlap universal)
  ≡ overlap;

assert [K : Cat]
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
      overlap)) ⊢
  @binary_scheme_chart_overlap_universal
    K S (@binary_scheme_chart_overlap_intro K S overlap universal)
  ≡ universal;

// Both product projections are whole arrows in the conventional slice.
assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_to_chart0 K S overlap
  : τ (Hom
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      (@binary_scheme_chart_overlap_restriction K S overlap)
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart0 K S)));

assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_to_chart1 K S overlap
  : τ (Hom
      (@Slice_cat K (@binary_site_relative_scheme_whole_object K S))
      (@binary_scheme_chart_overlap_restriction K S overlap)
      (@reflective_comm_ringed_space_cover_chart_restriction
        K
        (@binary_site_relative_scheme_global_cover K S)
        (@binary_site_relative_scheme_chart1 K S)));

// Whole slice-domain action supplies their actual arrows in K.
assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_domain_to_chart0 K S overlap
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
          (@binary_site_relative_scheme_chart0 K S))));

assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_domain_to_chart1 K S overlap
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
          (@binary_site_relative_scheme_chart1 K S))));

// The overlap ring is the global structure presheaf at the product domain.
assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_ring K S overlap
  ≡ @comm_ring_psh_value
      K
      (@binary_site_relative_scheme_underlying_psh K S)
      (@binary_scheme_chart_overlap_domain K S overlap);

// Both restrictions are the existing whole presheaf action into that ring.
assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_restriction0 K S overlap
  : τ (@CommRingHom
      (@binary_scheme_chart0_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap));

assert [K : Cat]
  [S : τ (@BinarySiteRelativeSchemePresentation K)]
  (overlap : τ (@BinarySchemeChartOverlapPresentation K S)) ⊢
  @binary_scheme_chart_overlap_restriction1 K S overlap
  : τ (@CommRingHom
      (@binary_scheme_chart1_structure_ring K S)
      (@binary_scheme_chart_overlap_ring K S overlap));
