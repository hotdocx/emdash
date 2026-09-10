/* The cover kernel maps into the original left-hand object of the first row. */
require open emdash.emdash3_2_homology_connecting_left_lift;
require open emdash.emdash3_2_homology_connecting_cover_kernel;
require open emdash.emdash3_2_kernel_maps;

symbol homology_connecting_cover_kernel_left_factor
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
  : τ (@HomPostcompFactor C A0 B0 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@comp_fapp0 C
    (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
    B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B0
    (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    X row0 row1 G incoming zero) H) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)))
≔ @is_contr_center _ (@computational_kernel_factor_contr C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B0 D0 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@short_exact_kernel_record C P t Ab A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
  (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
  (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 X row0 row1 G incoming zero) H)
    (@computational_kernel_map_cone C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0
      row1 G incoming zero) H) B0 D0
      (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
        B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@homology_connecting_cover_kernel C P t Ab A0 B0 X D0 D1 row0
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@short_exact_kernel_record
        C P t Ab A0 B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
        (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
        (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
        D1 X row0 row1 G incoming zero) H)
      (@homology_connecting_cover_diagram_factor C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
        A1 B1 D1 X row0 row1 G incoming zero) H)));

symbol homology_connecting_cover_kernel_left
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
  : τ (Hom C (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
    B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A0)
≔ @hom_postcomp_factor_arrow C A0 B0 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_dnext
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@comp_fapp0 C
  (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B0
  (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X
  row0 row1 G incoming zero) H) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H))
  (@homology_connecting_cover_kernel_left_factor C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H);

symbol homology_connecting_cover_kernel_left_reconstruction
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
    Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B0) (@comp_fapp0 C (@homology_connecting_cover_kernel_object C P t Ab A0 B0
    X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A0 B0
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0
    B0 D0 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0))
    (@homology_connecting_cover_kernel_left C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)) (@comp_fapp0 C
      (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B0
      (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)))
≔ @hom_postcomp_factor_path C A0 B0 (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_dnext
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@comp_fapp0 C
  (@homology_connecting_cover_kernel_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
  B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B0
  (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X
  row0 row1 G incoming zero) H) (@homology_connecting_cover_kernel_inclusion C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H))
  (@homology_connecting_cover_kernel_left_factor C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H);
