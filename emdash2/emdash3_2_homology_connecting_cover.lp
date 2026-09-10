/* First direct connecting step: pull a row epimorphism back along actual cycles.
   The existing kernel/difference pullback owns the cone and its universal data. */
require open emdash.emdash3_2_short_exact_rows;
require open emdash.emdash3_2_homology_family_records;
require open emdash.emdash3_2_abelian_fiber_pushout_stability;

symbol homology_connecting_cover
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (@ComputationalFiberProduct C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y B
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y
    Z right_pair H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P
    t Ab)) A B Y (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row)))
≔ @abelian_selected_fiber_product C P t Ab (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y B (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H)
  (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B Y
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row));

symbol homology_connecting_cover_object
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (Obj C)
≔ @computational_fiber_product_object C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y B
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
  right_pair H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A B Y (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row))
  (@homology_connecting_cover C P t Ab A B X Y Z row right_pair H);

symbol homology_connecting_cover_projection
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (Hom C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H))
≔ @computational_fiber_product_proj1 C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y B
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
  right_pair H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A B Y (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row))
  (@homology_connecting_cover C P t Ab A B X Y Z row right_pair H);

symbol homology_connecting_cover_middle
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (Hom C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) B)
≔ @computational_fiber_product_proj2 C P t (@abelian_stability_additive C P t Ab) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y B
  (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
  right_pair H) (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) A B Y (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row))
  (@homology_connecting_cover C P t Ab A B X Y Z row right_pair H);

symbol homology_connecting_cover_epic
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (@IsEpic C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H)
    (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H))
≔ @abelian_fiber_product_epic_projection C P t Ab (@homology_record_cycle_object C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y B (@homology_record_cycle_embedding C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H)
  (@computational_chain_pair_d C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B Y
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row))
    (@computational_short_exact_epic C P t (@computational_abelian_preabelian C P t Ab) A B Y (@computational_short_exact_row_pair C
      P t (@computational_abelian_preabelian C P t Ab) A B Y row)
      (@computational_short_exact_row_evidence C P t (@computational_abelian_preabelian C P t Ab) A B Y row));

symbol homology_connecting_cover_reconstruction
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (@= (Hom C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) Y)
      (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) B Y (@computational_chain_pair_d C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B Y
        (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row))
        (@homology_connecting_cover_middle C P t Ab A B X Y Z row right_pair H))
      (@comp_fapp0 C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
        (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y
        (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
        X Y Z right_pair H) (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H)))
≔ @eq_sym _ _ _ (@computational_fiber_product_compatibility_path C P t (@abelian_stability_additive C P t Ab)
  (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
  right_pair H) Y B (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) (@computational_chain_pair_d C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) A B Y
  (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian C P t Ab) A B Y row)) (@homology_connecting_cover C
  P t Ab A B X Y Z row right_pair H));
