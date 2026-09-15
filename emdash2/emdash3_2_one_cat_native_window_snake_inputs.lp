/* Whole general-snake input from the original four-row native homology window.
   Only the two original middle-column chain-zero laws are inputs. */
require open emdash.emdash3_2_one_cat_biproduct_family_zeros;
require open emdash.emdash3_2_one_cat_zero_cone_row_families;
require open emdash.emdash3_2_native_snake_inputs;

// a=[bₘ,i₀] is one whole coproduct mate on the original upper rows.
symbol one_cat_native_window_snake_incoming [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Rm R0 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  : τ (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))
≔ (@one_cat_copair_family K C C1 Prod t Add T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src) (@one_cat_zero_cone_row_family_incoming
  K C C1 t (@additive_terminal_object C Prod t Add) R0));

// c=⟨b₁,p₁⟩ is one whole product mate on the original lower rows.
symbol one_cat_native_window_snake_outgoing [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))))
≔ (@one_cat_product_family_pair K C C1 Prod (@additive_binary_products C Prod t Add)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1));

// The two column-zero laws and native row reconstruction derive c∘b₀∘a=0.
symbol one_cat_native_window_snake_triple_zero [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0))) (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))) (@comp_fapp0 (Functor_cat K C) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@comp_fapp0
  (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_incoming K C C1 Prod t Add T0 Rm R0 mm))) (@zero_arrow_family_zero_transf K C
  t (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0))) (@fapp0 (Functor_cat
  K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma
  (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))))
≔ (@one_cat_product_pair_precompose_zero_path K C C1 Prod t Add T0 (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt) (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K
  C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C),
  Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_incoming K C C1 Prod t Add T0 Rm R0 mm)) (@zero_cone_row_family_vertex_map K C
  t (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R1) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_incoming
  K C C1 Prod t Add T0 Rm R0 mm)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K
  C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (@Transf K C (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)) (λ v : τ (@Transf K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C)
  (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor
  K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) v
  (@one_cat_native_window_snake_incoming K C C1 Prod t Add T0 Rm R0 mm))) _ _ lower_zero)
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@one_cat_native_window_snake_incoming K C C1
  Prod t Add T0 Rm R0 mm)))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@one_cat_native_window_snake_incoming
  K C C1 Prod t Add T0 Rm R0 mm)) (@one_cat_copair_postcompose_zero_path K C C1 Prod t Add T0
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R0) (@comp_fapp0
  (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0
  walking_arrow_src)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) Rm R0 mm
  walking_arrow_src))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)) (@Transf K C
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)) (λ
  v : τ (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src)), (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R1) v)) _ _ upper_zero) (@one_cat_zero_family_postcompose_path K C
  C1 t (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R1)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat
  K C) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_zero_cone_row_family_incoming K C C1 t (@additive_terminal_object C Prod t Add) R0))) (@eq_trans _
  _ _ _ (@eq_ap (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))
  (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)) (λ
  v : τ (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_src)),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R0) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t (@additive_terminal_object C Prod t Add) R1) v)) _
  _ (@one_cat_zero_cone_row_incoming_square_path K C C1 t (@additive_terminal_object C Prod t Add) R0 R1 m0))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) (@zero_cone_row_family_outgoing K C t
  (@additive_terminal_object C Prod t Add) R1) (@one_cat_zero_cone_row_family_incoming K C C1 t
  (@additive_terminal_object C Prod t Add) R1) (@zero_cone_row_family_source_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt))
  (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)) (λ
  v : τ (@Transf K C (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)),
  (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t
  Add) R0) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt) v
  (@zero_cone_row_family_source_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0))) _ _
  (@one_cat_zero_family_chain_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_diagram_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@one_cat_zero_cone_row_family_transf K C C1 t (@additive_terminal_object C Prod t Add) R1)))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R1)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)
  (@zero_cone_row_family_source_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0)))))))));

// The original four-row window supplies a whole general-snake input, before K/Q or short-exactness.
symbol one_cat_native_window_snake_input [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C
  C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1))
≔ (@one_cat_native_snake_input K C C1 t (@additive_terminal_object C Prod t Add) T0 (@fapp0 (Functor_cat K
  (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor
  K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_incoming K C C1 Prod t Add T0 Rm R0 mm)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_triple_zero K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero));

// The resulting native input recovers the original whole a=[bₘ,i₀].
symbol one_cat_native_window_snake_input_incoming_path [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Rm R0 R1 R2 : τ (Functor K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add))))
  (mm : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) Rm R0))
  (m0 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R0 R1))
  (m1 : τ (@Transf K (@ZeroArrowCone_cat C t (@additive_terminal_object C Prod t Add)) R1 R2))
  (upper_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R1 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) Rm R0 mm walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src))))
  (lower_zero : τ (@= (@Transf K C (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod
  t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src)) (@comp_fapp0 (Functor_cat K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R1 R2 m1 walking_arrow_src) (@zero_cone_row_family_vertex_map K C t
  (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R2 walking_arrow_src))))
  : τ (@= (@Transf K C (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) Rm walking_arrow_src)
  (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add) R0)))
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0 walking_arrow_src))
  (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add) (@fapp0 (Functor_cat K (Product_cat C
  C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t (@additive_terminal_object C Prod t Add)
  R0))) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R0
  walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1
  walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K
  (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R2 walking_arrow_src)
  (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add) R1 walking_arrow_tgt)))
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1) (@one_cat_native_window_snake_input K
  C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero)) (@one_cat_native_window_snake_incoming K C
  C1 Prod t Add T0 Rm R0 mm))
≔ (@one_cat_native_snake_input_incoming_path K C C1 t (@additive_terminal_object C Prod t Add) T0 (@fapp0
  (Functor_cat K (Product_cat C C)) (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod)
  (@Struct_sigma (Functor K C) (λ _ : τ (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) Rm walking_arrow_src) (@zero_cone_row_family_source_func K C t
  (@additive_terminal_object C Prod t Add) R0))) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R0 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t
  (@additive_terminal_object C Prod t Add) R1 walking_arrow_src) (@fapp0 (Functor_cat K (Product_cat C C))
  (Functor_cat K C) (@comp_cat_cov_func K (Product_cat C C) C Prod) (@Struct_sigma (Functor K C) (λ _ : τ
  (Functor K C), Functor K C) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t
  Add) R2 walking_arrow_src) (@zero_cone_row_family_vertex_func K C t (@additive_terminal_object C Prod t Add)
  R1 walking_arrow_tgt))) (@one_cat_native_window_snake_incoming K C C1 Prod t Add T0 Rm R0 mm)
  (@zero_cone_row_family_vertex_map K C t (@additive_terminal_object C Prod t Add) R0 R1 m0 walking_arrow_src)
  (@one_cat_native_window_snake_outgoing K C C1 Prod t Add T0 R1 R2 m1)
  (@one_cat_native_window_snake_triple_zero K C C1 Prod t Add T0 Rm R0 R1 R2 mm m0 m1 upper_zero lower_zero));
