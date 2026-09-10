/* Direct connecting step: derive the lower-row kernel test from the existing
   cover, row-map factor and retained source cycles. No normal test is assumed. */
require open emdash.emdash3_2_homology_connecting_cover;
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_short_exact_universal_records;
require open emdash.emdash3_2_hom_factor_composition;
require open emdash.emdash3_2_preabelian_bimorphism_lemmas;

// The source pair uses the actual right-hand differential of this row map.
symbol homology_connecting_step_right_pair
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
  : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1)
≔ @computational_chain_pair_intro C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
  incoming (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) zero;

symbol homology_connecting_middle_differential
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
  : τ (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 X row0 row1 G incoming zero) H) B1)
≔ @comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
  D0 A1 B1 D1 X row0 row1 G incoming zero) H) B0 B1 (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P
  t (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H);

// p₁ ∘ (dB ∘ b) = (dR ∘ κ) ∘ e = 0.
symbol homology_connecting_middle_annihilation
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
  : τ (@= (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
    D0 A1 B1 D1 X row0 row1 G incoming zero) H) D1)
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
      B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1 D1 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero H))
    (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H) D1))
≔ @eq_trans _ _ _ _
    (@hom_factor_paste_path C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C
      P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive
      C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X
      row0 row1 G incoming zero) H) B0 D0 B1 D1
      (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1
        B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0)) (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
        (@homology_connecting_cover_middle C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
        D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G) (@homology_record_cycle_embedding C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
        row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
      (@homology_connecting_cover_reconstruction C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
        A1 B1 D1 X row0 row1 G incoming zero) H)
      (@eq_sym _ _ _ (@computational_chain_pair_map_lower_path C (@computational_homology_preadditive C P t
        (@computational_abelian_preabelian C P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A0 B0 D0 row0) (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)))
    (@preadditive_precompose_zero_path C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
      (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
      D1 X row0 row1 G incoming zero) H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t
      (@computational_abelian_preabelian C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0
      row1 G incoming zero) H) D1
      (@comp_fapp0 C (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian
        C P t Ab)) X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) D0 D1
        (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
        Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
        row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        X D0 D1 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H))
        (@homology_connecting_cover_projection C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
        A1 B1 D1 X row0 row1 G incoming zero) H)
      (@computational_kernel_annihilation C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        D0 D1 (@computational_chain_pair_map_prev C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C
        P t Ab)) A0 B0 D0 A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A0 B0 D0
        row0) (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1) G)
        (@homology_record_cycles C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X D0 D1
        (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)));

symbol homology_connecting_left_test
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
  : τ (@WeakKernelAnnihilator C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) B1 D1
    (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
    (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1
    X row0 row1 G incoming zero) H))
≔ @Struct_sigma (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
  A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1)
    (λ f : τ (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
      B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1), @= (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
      (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) D1)
      (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab
        A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1 D1 (@computational_chain_pair_d C (@computational_homology_preadditive
        C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
        (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) f)
      (@preadditive_hom_zero C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1
        D1 X row0 row1 G incoming zero) H) D1))
    (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
      (@homology_connecting_middle_annihilation C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H);

// The actual row kernel has object A₁ and inclusion i₁.
symbol homology_connecting_left_factor
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
  : τ (@HomPostcompFactor C A1 B1 (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
    (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H)
    (@computational_chain_pair_dnext C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1
    B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H))
≔ @is_contr_center _ (@computational_kernel_factor_contr C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) B1 D1 (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
  (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
    (@short_exact_kernel_record C P t Ab A1 B1 D1 (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P
      t Ab) A1 B1 D1 row1) (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1
      row1)) (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
      A1 B1 D1 X row0 row1 G incoming zero) H) (@homology_connecting_left_test C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming
      zero H));

symbol homology_connecting_left_lift
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
  : τ (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0 D0
    A1 B1 D1 X row0 row1 G incoming zero) H) A1)
≔ @hom_postcomp_factor_arrow C A1 B1 (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_dnext
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
  (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
  (@homology_connecting_left_factor C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H);

symbol homology_connecting_left_reconstruction
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
  : τ (@= (Hom C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0 B0
    D0 A1 B1 D1 X row0 row1 G incoming zero) H) B1)
    (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0 (@homology_connecting_step_right_pair C P t Ab A0
      B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) A1 B1 (@computational_chain_pair_dnext C (@computational_homology_preadditive C
      P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1 (@computational_short_exact_row_pair C P t
      (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1)) (@homology_connecting_left_lift C P t Ab A0 B0 D0 A1 B1 D1 X row0
      row1 G incoming zero H)) (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H))
≔ @hom_postcomp_factor_path C A1 B1 (@homology_connecting_cover_object C P t Ab A0 B0 X D0 D1 row0
  (@homology_connecting_step_right_pair C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero) H) (@computational_chain_pair_dnext
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A1 B1 D1
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A1 B1 D1 row1))
  (@homology_connecting_middle_differential C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H)
  (@homology_connecting_left_factor C P t Ab A0 B0 D0 A1 B1 D1 X row0 row1 G incoming zero H);
