/* Specialized coherent four-row window with whole functor/transfor fields. */
require open emdash.emdash3_2_short_exact_row_families;

/*
  Coherent row-family data for one four-row homology window.
  Rows and vertical maps are whole functors/transformations. The two
  pointwise chain-zero hypotheses are the existing reference-window data,
  not newly supplied naturality squares.
*/

symbol RowFamilyMiddleChainZero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (Ra Rb Rc : τ (@ShortExactRowFamily I C C1 P t PA T))
  (f : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Ra)
    (@short_exact_row_family_func I C C1 P t PA T Rb))) (g : τ (@Transf I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T Rb) (@short_exact_row_family_func I C C1 P t PA T Rc))) : Grpd
≔ @Pi_grpd (Obj I) (λ x : τ (Obj I), (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Ra) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rc) x)) walking_arrow_src)) (@comp_fapp0 C
  (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
  Ra) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
  Rb) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
  Rc) x)) walking_arrow_src) (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t PA) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rb) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_tgt) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rc) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rc) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rc) x)) walking_arrow_tgt)
  (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) (@fapp0 WalkingArrow_cat C
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_src) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_tgt)
  (@short_exact_row_family_at I C C1 P t PA T Rb x)) (@computational_short_exact_row_pair C P t PA (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rc) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rc) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rc) x)) walking_arrow_tgt)
  (@short_exact_row_family_at I C C1 P t PA T Rc x)) (@short_exact_row_family_transf_at I C C1 P t PA T Rb Rc g x))
  (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T)
  C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
  Ra) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
  Ra) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
  Ra) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_src) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_tgt)
  (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Ra) x)) (@fapp0 WalkingArrow_cat C
  (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Ra) x)) walking_arrow_src) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Ra) x)) walking_arrow_tgt)
  (@short_exact_row_family_at I C C1 P t PA T Ra x)) (@computational_short_exact_row_pair C P t PA (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rb) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
  (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
  (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rb) x)) walking_arrow_tgt)
  (@short_exact_row_family_at I C C1 P t PA T Rb x)) (@short_exact_row_family_transf_at I C C1 P t PA T Ra Rb f x)))
  (@preadditive_hom_zero C (@computational_homology_preadditive C P t PA) (@fapp0 WalkingArrow_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
  (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Ra) x)) walking_arrow_src) (@fapp0
  WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t
  T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rc) x)) walking_arrow_src))));

constant symbol HomologyWindowRows [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) : Grpd;

constant symbol homology_window_rows_intro [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (Rm : τ (@ShortExactRowFamily I C C1 P t PA T))
  (R0 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (R1 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (R2 : τ (@ShortExactRowFamily I C C1 P t PA T))
  (F : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T Rm)
    (@short_exact_row_family_func I C C1 P t PA T R0)))
  (G : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R0)
    (@short_exact_row_family_func I C C1 P t PA T R1)))
  (J : τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T R1)
    (@short_exact_row_family_func I C C1 P t PA T R2)))
  : τ (@HomologyWindowRows I C C1 P t PA T);

symbol homology_window_rows_rowm [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_window_rows_rowm _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ $v _ _ _ _ _ _) ↪ $v;

symbol homology_window_rows_row0 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_window_rows_row0 _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ _ $v _ _ _ _ _) ↪ $v;

symbol homology_window_rows_row1 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_window_rows_row1 _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ _ _ $v _ _ _ _) ↪ $v;

symbol homology_window_rows_row2 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@ShortExactRowFamily I C C1 P t PA T);
rule @homology_window_rows_row2 _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ _ _ _ $v _ _ _) ↪ $v;

symbol homology_window_rows_F [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_rows_rowm I C C1 P
    t PA T rows)) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_rows_row0 I C C1 P t PA T rows)));
rule @homology_window_rows_F _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ _ _ _ _ $v _ _) ↪ $v;

symbol homology_window_rows_G [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_rows_row0 I C C1 P
    t PA T rows)) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_rows_row1 I C C1 P t PA T rows)));
rule @homology_window_rows_G _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ _ _ _ _ _ $v _) ↪ $v;

symbol homology_window_rows_J [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : τ
    (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_rows_row1 I C C1 P
    t PA T rows)) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_rows_row2 I C C1 P t PA T rows)));
rule @homology_window_rows_J _ _ _ _ _ _ _
  (@homology_window_rows_intro _ _ _ _ _ _ _ _ _ _ _ _ _ $v) ↪ $v;

symbol HomologyWindowUpperZero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : Grpd
≔ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_window_rows_rowm I C C1 P t PA T rows) (@homology_window_rows_row0 I
  C C1 P t PA T rows) (@homology_window_rows_row1 I C C1 P t PA T rows) (@homology_window_rows_F I C C1 P t PA T rows)
  (@homology_window_rows_G I C C1 P t PA T rows));
symbol HomologyWindowLowerZero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (rows : τ (@HomologyWindowRows I C C1 P t PA T)) : Grpd
≔ (@RowFamilyMiddleChainZero I C C1 P t PA T (@homology_window_rows_row0 I C C1 P t PA T rows) (@homology_window_rows_row1 I
  C C1 P t PA T rows) (@homology_window_rows_row2 I C C1 P t PA T rows) (@homology_window_rows_G I C C1 P t PA T rows)
  (@homology_window_rows_J I C C1 P t PA T rows));

constant symbol HomologyWindowFamily [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) : Grpd;

constant symbol homology_window_family_intro [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (rows : τ (@HomologyWindowRows I C C1 P t PA T)) (upper : τ (@HomologyWindowUpperZero I C C1 P t PA T rows)) (lower : τ
    (@HomologyWindowLowerZero I C C1 P t PA T rows))
  : τ (@HomologyWindowFamily I C C1 P t PA T);

symbol homology_window_family_rows [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@HomologyWindowRows I C C1 P t PA T);
rule @homology_window_family_rows _ _ _ _ _ _ _
  (@homology_window_family_intro _ _ _ _ _ _ _ $rows _ _) ↪ $rows;

symbol homology_window_family_zero_data [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T))
  : τ (@Product_grpd (@HomologyWindowUpperZero I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window))
    (@HomologyWindowLowerZero I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window)));
rule @homology_window_family_zero_data _ _ _ _ _ _ _
  (@homology_window_family_intro $I $C $C1 $P $t $PA $T $rows $u $l)
  ↪ @Product_pair_grpd
      (@HomologyWindowUpperZero $I $C $C1 $P $t $PA $T $rows)
      (@HomologyWindowLowerZero $I $C $C1 $P $t $PA $T $rows) $u $l;

symbol homology_window_family_rowm [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@ShortExactRowFamily I C C1 P t PA T)
≔ @homology_window_rows_rowm I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_row0 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@ShortExactRowFamily I C C1 P t PA T)
≔ @homology_window_rows_row0 I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_row1 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@ShortExactRowFamily I C C1 P t PA T)
≔ @homology_window_rows_row1 I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_row2 [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@ShortExactRowFamily I C C1 P t PA T)
≔ @homology_window_rows_row2 I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_F [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C
    C1 P t PA T window)) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T
    window)))
≔ @homology_window_rows_F I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_G [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C
    C1 P t PA T window)) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)))
≔ @homology_window_rows_G I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_J [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T)) :
    τ (@Transf I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C
    C1 P t PA T window)) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)))
≔ @homology_window_rows_J I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window);

symbol homology_window_family_upper_zero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T))
  : τ (@HomologyWindowUpperZero I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window))
≔ sigma_Fst (@homology_window_family_zero_data I C C1 P t PA T window);

symbol homology_window_family_lower_zero [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t)) (window : τ (@HomologyWindowFamily I C C1 P t PA T))
  : τ (@HomologyWindowLowerZero I C C1 P t PA T (@homology_window_family_rows I C C1 P t PA T window))
≔ sigma_Snd (@homology_window_family_zero_data I C C1 P t PA T window);

/* Point views of the retained whole row-window data. */

symbol homology_window_rowm_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalShortExactRow C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0
    I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T
    window)) x)) walking_arrow_tgt))
≔ @short_exact_row_family_at I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window) x;

symbol homology_window_row0_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalShortExactRow C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0
    I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T
    window)) x)) walking_arrow_tgt))
≔ @short_exact_row_family_at I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window) x;

symbol homology_window_row1_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalShortExactRow C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0
    I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) walking_arrow_tgt))
≔ @short_exact_row_family_at I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window) x;

symbol homology_window_row2_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalShortExactRow C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0
    I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)) x)) walking_arrow_tgt))
≔ @short_exact_row_family_at I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T window) x;

symbol homology_window_F_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t
    PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@homology_window_rowm_at I C C1 P t PA T window x)) (@computational_short_exact_row_pair C P t PA
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@homology_window_row0_at I C C1 P t PA T window x)))
≔ @short_exact_row_family_transf_at I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)
  (@homology_window_family_row0 I C C1 P t PA T window) (@homology_window_family_F I C C1 P t PA T window) x;

symbol homology_window_G_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t
    PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@homology_window_row0_at I C C1 P t PA T window x)) (@computational_short_exact_row_pair C P t PA
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@homology_window_row1_at I C C1 P t PA T window x)))
≔ @short_exact_row_family_transf_at I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)
  (@homology_window_family_row1 I C C1 P t PA T window) (@homology_window_family_G I C C1 P t PA T window) x;

symbol homology_window_J_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@ComputationalChainPairMap C (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t
    PA (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@homology_window_row1_at I C C1 P t PA T window x)) (@computational_short_exact_row_pair C P t PA
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@homology_window_row2_at I C C1 P t PA T window x)))
≔ @short_exact_row_family_transf_at I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)
  (@homology_window_family_row2 I C C1 P t PA T window) (@homology_window_family_J I C C1 P t PA T window) x;

symbol homology_window_upper_zero_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) walking_arrow_src)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) walking_arrow_src) (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t PA)
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row0_at I C C1 P t PA T
    window x)) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row1_at I C C1 P t PA T
    window x)) (@homology_window_G_at I C C1 P t PA T window x)) (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1
    P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T
    window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T
    window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_rowm I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_rowm_at I C C1 P t PA T
    window x)) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row0_at I C C1 P t PA T
    window x)) (@homology_window_F_at I C C1 P t PA T window x))) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t PA) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_rowm I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_src)))
≔ (@homology_window_family_upper_zero I C C1 P t PA T window) x;

symbol homology_window_lower_zero_at [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (window : τ (@HomologyWindowFamily I C C1 P t PA T)) (x : τ (Obj I))
  : τ (@= (Hom C (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)) x)) walking_arrow_src)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)) x)) walking_arrow_src) (@computational_chain_pair_map_middle C (@computational_homology_preadditive C P t PA)
    (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0
    WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C
    t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I
    C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
    WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T
    window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row1_at I C C1 P t PA T
    window x)) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row2 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row2_at I C C1 P t PA T
    window x)) (@homology_window_J_at I C C1 P t PA T window x)) (@computational_chain_pair_map_middle C
    (@computational_homology_preadditive C P t PA) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
    (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1
    P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T
    window)) x)) walking_arrow_tgt) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0
    (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I
    (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T
    window)) x)) walking_arrow_tgt) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row0 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row0_at I C C1 P t PA T
    window x)) (@computational_short_exact_row_pair C P t PA (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_first_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row1 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row1 I C C1 P t PA T window)) x)) walking_arrow_tgt) (@homology_window_row1_at I C C1 P t PA T
    window x)) (@homology_window_G_at I C C1 P t PA T window x))) (@preadditive_hom_zero C
    (@computational_homology_preadditive C P t PA) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T)
    (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T)
    (@short_exact_row_family_func I C C1 P t PA T (@homology_window_family_row0 I C C1 P t PA T window)) x))
    walking_arrow_src) (@fapp0 WalkingArrow_cat C (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@fapp0 I (@ZeroArrowCone_cat C t T) (@short_exact_row_family_func I C C1 P t PA T
    (@homology_window_family_row2 I C C1 P t PA T window)) x)) walking_arrow_src)))
≔ (@homology_window_family_lower_zero I C C1 P t PA T window) x;
