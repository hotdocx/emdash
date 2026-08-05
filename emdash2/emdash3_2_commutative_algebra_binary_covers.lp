/*
  Constructive binary refinements of selected ringed-space covers.

  Two selected members of a covering sieve are not by themselves a binary
  cover.  The generation capability below instead gives, for every arrow in
  the selected covering sieve, a Boolean-selected chart, an actual factor map,
  and the triangle identifying its composite with the original arrow.  Thus
  the two charts generate the retained covering sieve: generation gives one
  inclusion, while their retained sieve membership gives the other.

  The representation is deliberately witness-rich and computational.  It
  constructs no generated sieve and needs no propositional truncation.  Its
  closure under further restriction follows by generic composition; no
  naturality, restriction, overlap, or cocycle field is stored.  This
  transparent module adds no rules and makes no affineness or scheme claim.
*/

require open emdash.emdash3_2_commutative_algebra_ringed_space_covers;

// One actual factorization of a cover arrow through a selected chart.
symbol CoverChartFactorization
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  : Grpd
≔ `Σ_ h : τ (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart)),
    @= (Hom K
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
        h);

symbol cover_chart_factorization_intro
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
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
      h)))
  : τ (@CoverChartFactorization K P chart q)
≔ @Struct_sigma
    (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart))
    (λ h0 : τ (Hom K
        (@into_restr_domain
          K
          (@reflective_comm_ringed_space_cover_whole_object K P)
          q)
        (@reflective_comm_ringed_space_cover_chart_domain K P chart)),
      @= (Hom K
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
          h0))
    h triangle;

symbol cover_chart_factorization_map
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@CoverChartFactorization K P chart q))
  : τ (Hom K
      (@into_restr_domain
        K
        (@reflective_comm_ringed_space_cover_whole_object K P)
        q)
      (@reflective_comm_ringed_space_cover_chart_domain K P chart))
≔ sigma_Fst factor;

symbol cover_chart_factorization_triangle
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@CoverChartFactorization K P chart q))
  : τ (@= (Hom K
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
      (@cover_chart_factorization_map K P chart q factor)))
≔ sigma_Snd factor;

// Witness-rich disjunction between factorization through chart 0 or chart 1.
symbol BinaryCoverChartFactorization
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  : Grpd
≔ `Σ_ side : τ Bool_grpd,
    @bool_elim
      (λ _ : τ Bool_grpd, Grpd_grpd)
      (@CoverChartFactorization K P chart0 q)
      (@CoverChartFactorization K P chart1 q)
      side;

symbol binary_cover_chart_factorization_left
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@CoverChartFactorization K P chart0 q))
  : τ (@BinaryCoverChartFactorization K P chart0 chart1 q)
≔ @Struct_sigma
    Bool_grpd
    (λ side : τ Bool_grpd,
      @bool_elim
        (λ _ : τ Bool_grpd, Grpd_grpd)
        (@CoverChartFactorization K P chart0 q)
        (@CoverChartFactorization K P chart1 q)
        side)
    false factor;

symbol binary_cover_chart_factorization_right
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@CoverChartFactorization K P chart1 q))
  : τ (@BinaryCoverChartFactorization K P chart0 chart1 q)
≔ @Struct_sigma
    Bool_grpd
    (λ side : τ Bool_grpd,
      @bool_elim
        (λ _ : τ Bool_grpd, Grpd_grpd)
        (@CoverChartFactorization K P chart0 q)
        (@CoverChartFactorization K P chart1 q)
        side)
    true factor;

symbol binary_cover_chart_factorization_side
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@BinaryCoverChartFactorization K P chart0 chart1 q))
  : τ Bool_grpd
≔ sigma_Fst factor;

symbol binary_cover_chart_factorization_evidence
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  [q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))]
  (factor : τ (@BinaryCoverChartFactorization K P chart0 chart1 q))
  : τ (@bool_elim
      (λ _ : τ Bool_grpd, Grpd_grpd)
      (@CoverChartFactorization K P chart0 q)
      (@CoverChartFactorization K P chart1 q)
      (@binary_cover_chart_factorization_side
        K P chart0 chart1 q factor))
≔ sigma_Snd factor;

// Every arrow in the retained covering sieve factors through one chart.
symbol BinarySelectedCoverGeneration
  [K : Cat]
  (P : τ (@ReflectiveCommRingedSpaceCover K))
  (chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P))
  : Grpd
≔ @Pi_grpd
    (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P)))
    (λ q : τ (Obj (@Into_restr_cat K
        (@reflective_comm_ringed_space_cover_whole_object K P))),
      @Function_grpd
        (@SieveMembership
          K
          (@reflective_comm_ringed_space_cover_whole_object K P)
          (@reflective_comm_ringed_space_cover_sieve K P)
          q)
        (@BinaryCoverChartFactorization K P chart0 chart1 q));

symbol binary_selected_cover_generation_at
  [K : Cat]
  [P : τ (@ReflectiveCommRingedSpaceCover K)]
  [chart0 chart1 : τ (@ReflectiveCommRingedSpaceCoverChart K P)]
  (generation : τ (@BinarySelectedCoverGeneration K P chart0 chart1))
  (q : τ (Obj (@Into_restr_cat K
      (@reflective_comm_ringed_space_cover_whole_object K P))))
  (member : τ (@SieveMembership
      K
      (@reflective_comm_ringed_space_cover_whole_object K P)
      (@reflective_comm_ringed_space_cover_sieve K P)
      q))
  : τ (@BinaryCoverChartFactorization K P chart0 chart1 q)
≔ generation q member;
