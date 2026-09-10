/* On the cover kernel, the left lift is the actual incoming boundary. */
require open emdash.emdash3_2_homology_connecting_cover_kernel_lift;

symbol homology_connecting_left_restricted_factor
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (incoming : τ (Hom C X D0))
  (zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero)))
  : τ (@HomPostcompFactor C A1 B1 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@comp_fapp0 C
    (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
    B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1
    (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
    (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 X row0 row1 G incoming zero) H)))
≔ @hom_postcomp_factor_paste C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
  (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X
  row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair
  C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A1 B1
    (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 X row0 row1 G incoming zero) H) (@id C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H))
      (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
      B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@id C
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H)) (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G
      incoming zero H)
    (@hom_postcomp_factor_intro C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@id C
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H)) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
      (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
      D0 A1 B1 D1 X row0 row1 G incoming zero) H)
      (@eq_refl (Hom C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C
        P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H))
        (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
        B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)))
    (@homology_connecting_left_factor C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H);

symbol homology_connecting_left_boundary_factor
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (incoming : τ (Hom C X D0))
  (zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero)))
  : τ (@HomPostcompFactor C A1 B1 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@comp_fapp0 C
    (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
    B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1
    (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
    (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 X row0 row1 G incoming zero) H)))
≔ @hom_postcomp_factor_paste C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
  (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X
  row0 row1 G incoming zero) H) A0 B0 A1 B1
    (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@computational_chain_pair_dnext C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
      (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_kernel_left_factor C P t Ab A0 B0
      D0 A1 B1 D1 X row0 row1 G incoming zero H)
    (@computational_chain_pair_map_upper C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G);

symbol homology_connecting_left_on_cover_kernel_path
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A0 B0 D0 A1 B1 D1 X : τ (Obj C)]
  (row0 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0))
  (row1 : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1))
  (G : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)))
  (incoming : τ (Hom C X D0))
  (zero : τ (@= (Hom C X D1) (@comp_fapp0 C X D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) incoming)
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D1)))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero)))
  : τ (@= (Hom C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t
    Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A1) (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0
    X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
    (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    X row0 row1 G incoming zero) H) A1 (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
    (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 X row0 row1 G incoming zero) H))
    (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t
      Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A0 A1 (@computational_chain_pair_map_next C
      (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
      (@homology_connecting_cover_kernel_left C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)))
≔ (@computational_short_exact_monic C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 (@computational_short_exact_row_pair
  C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) (@computational_short_exact_row_evidence C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
    (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t
      Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A1
      (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
      (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
      D0 A1 B1 D1 X row0 row1 G incoming zero) H)) (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1
      row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A0 A1
      (@computational_chain_pair_map_next C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
      (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
      (@homology_connecting_cover_kernel_left C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H))
    (@eq_trans _ _ _ _
      (@hom_postcomp_factor_path C A1 B1 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
        (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C
        P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1
        (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
        (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
        B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)) (@homology_connecting_left_restricted_factor C P t Ab A0 B0 D0 A1 B1 D1 X
        row0 row1 G incoming zero H))
      (@eq_sym _ _ _ (@hom_postcomp_factor_path C A1 B1 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
        (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C
        P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1
        (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
        (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
        B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)) (@homology_connecting_left_boundary_factor C P t Ab A0 B0 D0 A1 B1 D1 X row0
        row1 G incoming zero H))));
