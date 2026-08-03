/*
  Reviewer for constructive binary refinements of selected covers.

  Each retained cover arrow chooses one of two charts together with an actual
  factor map and triangle.  The choice and factorization data compute through
  Bool and Sigma owners.  No generated sieve, truncation, external
  restriction law, affineness, or scheme claim is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_binary_covers;

// A literal chart factorization exposes its selected map.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (h : τ (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)))
  (triangle : τ (@= (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_whole_object K P))
    (@into_restr_arrow
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      q)
    (@comp_fapp0
      K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_chart_arrow K P chart)
      h))) ⊢
  @cover_chart_factorization_map
    K P chart q
    (@cover_chart_factorization_intro K P chart q h triangle)
  ≡ h;

// Its retained triangle is the exact constructor field.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (h : τ (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)))
  (triangle : τ (@= (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_whole_object K P))
    (@into_restr_arrow
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      q)
    (@comp_fapp0
      K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_chart_arrow K P chart)
      h))) ⊢
  @cover_chart_factorization_triangle
    K P chart q
    (@cover_chart_factorization_intro K P chart q h triangle)
  ≡ triangle;

// Boolean branch constructors expose their selected sides.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (factor : τ (@CoverChartFactorization K P chart0 q)) ⊢
  @binary_cover_chart_factorization_side
    K P chart0 chart1 q
    (@binary_cover_chart_factorization_left
      K P chart0 chart1 q factor)
  ≡ false;

assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (factor : τ (@CoverChartFactorization K P chart1 q)) ⊢
  @binary_cover_chart_factorization_side
    K P chart0 chart1 q
    (@binary_cover_chart_factorization_right
      K P chart0 chart1 q factor)
  ≡ true;

// Branch evidence computes back to the selected factorization.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (factor : τ (@CoverChartFactorization K P chart0 q)) ⊢
  @binary_cover_chart_factorization_evidence
    K P chart0 chart1 q
    (@binary_cover_chart_factorization_left
      K P chart0 chart1 q factor)
  ≡ factor;

// Generation evidence evaluates by ordinary internal function application.
assert [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      q)) ⊢
  @binary_selected_cover_generation_at
    K P chart0 chart1 generation q member
  ≡ generation q member;
