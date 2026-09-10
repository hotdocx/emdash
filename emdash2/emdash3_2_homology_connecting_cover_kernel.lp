/* Retain the exact cover kernel used by the normal-epi capability. */
require open emdash.emdash3_2_homology_connecting_cover;
require open emdash.emdash3_2_hom_factor_spaces;

symbol homology_connecting_cover_kernel
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (@ComputationalKernel C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
    (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H)
    (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H))
≔ (@preabelian_kernels C P t (@computational_abelian_preabelian C P t Ab)) (@homology_connecting_cover_object C P t Ab A B X Y Z row
  right_pair H) (@homology_record_cycle_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
  Ab)) X Y Z right_pair H) (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H);

symbol homology_connecting_cover_kernel_object
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (Obj C)
≔ @computational_kernel_object C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H)
  (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H) (@homology_connecting_cover_kernel C P t Ab A B X Y Z
  row right_pair H);

symbol homology_connecting_cover_kernel_inclusion
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (Hom C (@homology_connecting_cover_kernel_object C P t Ab A B X Y Z row right_pair H) (@homology_connecting_cover_object C P t
    Ab A B X Y Z row right_pair H))
≔ @computational_kernel_morphism C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab))
  (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
  (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H)
  (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H) (@homology_connecting_cover_kernel C P t Ab A B X Y Z
  row right_pair H);

// The existing pullback supplies this arrow-category factor.
symbol homology_connecting_cover_diagram_factor
  [C : Cat] [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Ab : τ (@ComputationalAbelianCategory C P t))
  [A B X Y Z : τ (Obj C)]
  (row : τ (@ComputationalShortExactRow C P t (@computational_abelian_preabelian C P t Ab) A B Y))
  (right_pair : τ (@ComputationalChainPair C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t
    Ab)) X Y Z))
  (H : τ (@HomologyRecord C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z
    right_pair))
  : τ (@HomPrecompFactor C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object C
    (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y
    (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H) (@comp_fapp0 C (@homology_connecting_cover_object C
    P t Ab A B X Y Z row right_pair H) B Y (@computational_chain_pair_d C (@computational_homology_preadditive C P t
    (@computational_abelian_preabelian C P t Ab)) A B Y (@computational_short_exact_row_pair C P t
    (@computational_abelian_preabelian C P t Ab) A B Y row)) (@homology_connecting_cover_middle C P t Ab A B X Y Z row right_pair
    H)))
≔ @hom_precomp_factor_intro C (@homology_connecting_cover_object C P t Ab A B X Y Z row right_pair H) (@homology_record_cycle_object
  C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y Z right_pair H) Y
  (@homology_connecting_cover_projection C P t Ab A B X Y Z row right_pair H) (@comp_fapp0 C (@homology_connecting_cover_object C P
  t Ab A B X Y Z row right_pair H) B Y (@computational_chain_pair_d C (@computational_homology_preadditive C P t
  (@computational_abelian_preabelian C P t Ab)) A B Y (@computational_short_exact_row_pair C P t (@computational_abelian_preabelian
  C P t Ab) A B Y row)) (@homology_connecting_cover_middle C P t Ab A B X Y Z row right_pair H))
    (@homology_record_cycle_embedding C (@computational_homology_preadditive C P t (@computational_abelian_preabelian C P t Ab)) X Y
      Z right_pair H) (@eq_sym _ _ _ (@homology_connecting_cover_reconstruction C P t Ab A B X Y Z row right_pair H));
