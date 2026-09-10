/* Every constructor projection, and a mismatched-data negative. */
require open emdash.emdash3_2_homology_window_families;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_rowm I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ Rm;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_row0 I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ R0;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_row1 I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ R1;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_row2 I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ R2;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_F I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ F;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_G I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ G;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
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
    (@short_exact_row_family_func I C C1 P t PA T R2))) ⊢
  @homology_window_rows_J I C C1 P t PA T (@homology_window_rows_intro I C C1 P t PA T Rm R0 R1 R2 F G J) ≡ J;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (rows : τ (@HomologyWindowRows I C C1 P t PA T))
  (upper : τ (@HomologyWindowUpperZero I C C1 P t PA T rows))
  (lower : τ (@HomologyWindowLowerZero I C C1 P t PA T rows)) ⊢ @homology_window_family_rows I C C1 P t PA T
    (@homology_window_family_intro I C C1 P t PA T rows upper lower) ≡ rows;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (rows : τ (@HomologyWindowRows I C C1 P t PA T))
  (upper : τ (@HomologyWindowUpperZero I C C1 P t PA T rows))
  (lower : τ (@HomologyWindowLowerZero I C C1 P t PA T rows)) ⊢ @homology_window_family_upper_zero I C C1 P t PA T
    (@homology_window_family_intro I C C1 P t PA T rows upper lower) ≡ upper;

assert [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (rows : τ (@HomologyWindowRows I C C1 P t PA T))
  (upper : τ (@HomologyWindowUpperZero I C C1 P t PA T rows))
  (lower : τ (@HomologyWindowLowerZero I C C1 P t PA T rows)) ⊢ @homology_window_family_lower_zero I C C1 P t PA T
    (@homology_window_family_intro I C C1 P t PA T rows upper lower) ≡ lower;

assertnot [I C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (PA : τ (@PreAbelianCategory C P t)) (T : τ (@TerminalObject C t))
  (rows : τ (@HomologyWindowRows I C C1 P t PA T))
  (upper : τ (@HomologyWindowUpperZero I C C1 P t PA T rows))
  (lower : τ (@HomologyWindowLowerZero I C C1 P t PA T rows)) (bad : τ (Obj I)) ⊢
  @homology_window_family_intro I C C1 P t PA T rows bad lower
    : τ (@HomologyWindowFamily I C C1 P t PA T);
