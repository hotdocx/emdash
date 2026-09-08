/* Retained factors, native side actions, and iterable whole comparisons. */
require open emdash.emdash3_2_hom_factor_cubical;

// postcomp: retain the actual native cell, with the correct orientation.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u))) ⊢
  sigma_Snd (sigma_Snd
    (@hom_postcomp_factor_square C A0 B0 A1 B1 u v b factor))
  ≡ @path_to_hom (Hom_cat C A0 B1)
      (@comp_fapp0 C A0 B0 B1 b u)
      (@comp_fapp0 C A0 A1 B1 v (@hom_postcomp_factor_arrow C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u) factor))
      (@eq_sym (Hom C A0 B1) _ _
        (@hom_postcomp_factor_path C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u) factor));
// precomp: retain the actual native cell, with the correct orientation.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a))) ⊢
  sigma_Snd (sigma_Snd
    (@hom_precomp_factor_square C A0 B0 A1 B1 u v a factor))
  ≡ @path_to_hom (Hom_cat C A0 B1)
      (@comp_fapp0 C A0 B0 B1 (@hom_precomp_factor_arrow C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a) factor) u)
      (@comp_fapp0 C A0 A1 B1 v a)
      (@hom_precomp_factor_path C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a) factor);

// postcomp: source action returns the retained side arrow.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u))) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)
    (@hom_postcomp_factor_square C A0 B0 A1 B1 u v b factor)
  ≡ @hom_postcomp_factor_arrow C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u) factor;

// postcomp: target action returns the retained side arrow.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u))) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)
    (@hom_postcomp_factor_square C A0 B0 A1 B1 u v b factor)
  ≡ b;

// postcomp: the whole comparison projects to the same square.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u))) ⊢
  @fapp0 _ _ (@hom_postcomp_factor_square_func C A0 B0 A1 B1 u v b) factor
  ≡ @hom_postcomp_factor_square C A0 B0 A1 B1 u v b factor;

// postcomp: a further hom action is a whole functor, not a capped cell.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (b : τ (Hom C B0 B1))
  (factor : τ (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u)))
  (other : τ (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u))) ⊢
  @fapp1_func _ _ (@hom_postcomp_factor_square_func C A0 B0 A1 B1 u v b) factor other
  : τ (Functor
      (Hom_cat (Path_cat (@HomPostcompFactor C A1 B1 A0 v (@comp_fapp0 C A0 B0 B1 b u))) factor other)
      (Hom_cat
        (Hom_cat (@LaxArrow_cat C)
          (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v))
        (@hom_postcomp_factor_square C A0 B0 A1 B1 u v b factor)
        (@hom_postcomp_factor_square C A0 B0 A1 B1 u v b other)));

// precomp: source action returns the retained side arrow.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a))) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)
    (@hom_precomp_factor_square C A0 B0 A1 B1 u v a factor)
  ≡ a;

// precomp: target action returns the retained side arrow.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a))) ⊢
  @fapp1_fapp0 (@LaxArrow_cat C) C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v)
    (@hom_precomp_factor_square C A0 B0 A1 B1 u v a factor)
  ≡ @hom_precomp_factor_arrow C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a) factor;

// precomp: the whole comparison projects to the same square.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a))) ⊢
  @fapp0 _ _ (@hom_precomp_factor_square_func C A0 B0 A1 B1 u v a) factor
  ≡ @hom_precomp_factor_square C A0 B0 A1 B1 u v a factor;

// precomp: a further hom action is a whole functor, not a capped cell.
assert
  [C : Cat] [A0 B0 A1 B1 : τ (Obj C)]
  (u : τ (Hom C A0 B0)) (v : τ (Hom C A1 B1))
  (a : τ (Hom C A0 A1))
  (factor : τ (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a)))
  (other : τ (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a))) ⊢
  @fapp1_func _ _ (@hom_precomp_factor_square_func C A0 B0 A1 B1 u v a) factor other
  : τ (Functor
      (Hom_cat (Path_cat (@HomPrecompFactor C A0 B0 B1 u (@comp_fapp0 C A0 A1 B1 v a))) factor other)
      (Hom_cat
        (Hom_cat (@LaxArrow_cat C)
          (@lax_edge C A0 B0 u) (@lax_edge C A1 B1 v))
        (@hom_precomp_factor_square C A0 B0 A1 B1 u v a factor)
        (@hom_precomp_factor_square C A0 B0 A1 B1 u v a other)));
