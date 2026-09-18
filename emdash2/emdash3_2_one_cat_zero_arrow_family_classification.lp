/* Whole classification of an ordinary zero-arrow family.
   Gamma retains A,D,h. Its source/target comparisons retain their original
   inverse data, and T∘tau_Gamma ≅ h∘J(S) is a whole modification.
   All operations are derived from the public comma classifier and the
   existing ordinary modification introduction; no caller square is added. */

require open emdash.emdash3_2_represented_comma_families;

require open emdash.emdash3_2_one_cat_zero_cones;

require open emdash.emdash3_2_one_cat_modifications;

// Classify the supplied whole zero-arrow family by Γ.
symbol one_cat_zero_arrow_family_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (Functor B (@ZeroArrowCone_cat C t T))
≔ @represented_comma_family_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  A D h;

// The actual source projection p∘Γ.
symbol one_cat_zero_arrow_family_source_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (Functor B C)
≔ @represented_comma_family_source_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A D h;

// The actual target projection q∘Γ.
symbol one_cat_zero_arrow_family_target_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @represented_comma_family_target_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A D h;

// The original universal τ whiskered by Γ.
symbol one_cat_zero_arrow_family_universal_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) (@one_cat_zero_arrow_family_target_func B C C1 t T A D h))
≔ @transf_prewhisker B (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@one_cat_zero_arrow_family_func B C C1 t T A D h)
  (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@zero_arrow_cone_first_func C t T))
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T);

// The source comparison inherited from the public comma classifier.
symbol one_cat_zero_arrow_family_source_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@Transf B C (@one_cat_zero_arrow_family_source_func B C C1 t T A D h) A)
≔ @represented_comma_family_source_to B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A D h;

// The target comparison, using the ordinary diagram-category profile.
symbol one_cat_zero_arrow_family_target_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@one_cat_zero_arrow_family_target_func B C C1 t T A D h) D)
≔ @one_cat_represented_comma_family_target_to B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  T) A D h (@one_cat_functor_category WalkingArrow_cat C C1);

// The whole composite T∘τΓ.
symbol one_cat_zero_arrow_family_triangle_left [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
≔ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) (@one_cat_zero_arrow_family_target_func
  B C C1 t T A D h) D
  (@one_cat_zero_arrow_family_target_to B C C1 t T A D h) (@one_cat_zero_arrow_family_universal_transf B C C1 t T A D h);

// The whole composite h∘J(S).
symbol one_cat_zero_arrow_family_triangle_right [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
≔ @comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D h
  (@transf_postwhisker B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C
  C1 t T A D h) A (@one_cat_zero_arrow_family_source_to B C C1 t T A D h));

protected symbol zero_arrow_family_triangle_to [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (Hom (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
  (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h))
≔ @one_cat_modification B (Functor_cat WalkingArrow_cat C) (@one_cat_functor_category
  WalkingArrow_cat C C1)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t
  T A D h)
   (λ x : τ (Obj B), @id (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) x)
  (@fapp0 B (Functor_cat WalkingArrow_cat C) D x))
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat
  C) (@terminal_arrow_diagram_func C t T) A) D x h));

protected symbol zero_arrow_family_triangle_from [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (Hom (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
  (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h))
≔ @one_cat_modification B (Functor_cat WalkingArrow_cat C) (@one_cat_functor_category
  WalkingArrow_cat C C1)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t
  T A D h)
   (λ x : τ (Obj B), @id (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) x)
  (@fapp0 B (Functor_cat WalkingArrow_cat C) D x))
      (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat
  C) (@terminal_arrow_diagram_func C t T) A) D x h));

protected symbol zero_arrow_family_triangle_left_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@= (Hom (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
  (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)) (@comp_fapp0 (@Transf_cat
  B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T
  A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)
  (@zero_arrow_family_triangle_from B C C1 t T A D h) (@zero_arrow_family_triangle_to B C C1 t T A D h)) (@id (@Transf_cat B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T
  A D h)))
≔ @is_contr_center (@= (Hom (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)) (@comp_fapp0
  (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T
  A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)
  (@zero_arrow_family_triangle_from B C C1 t T A D h) (@zero_arrow_family_triangle_to B C C1 t T A D h)) (@id (@Transf_cat B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T
  A D h)))
   ((@discrete_hom_is_prop (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) ((@one_cat_functor_category B (Functor_cat WalkingArrow_cat C) (@one_cat_functor_category
  WalkingArrow_cat C C1)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T
  A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)) (@comp_fapp0 (@Transf_cat B (Functor_cat WalkingArrow_cat
  C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1
  t T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@zero_arrow_family_triangle_from B C C1 t T A D h)
  (@zero_arrow_family_triangle_to B C C1 t T A D h)) (@id (@Transf_cat B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func
  B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h)));

protected symbol zero_arrow_family_triangle_right_law [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (@= (Hom (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
  (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)) (@comp_fapp0
  (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t
  T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)
  (@zero_arrow_family_triangle_to B C C1 t T A D h) (@zero_arrow_family_triangle_from B C C1 t T A D h)) (@id (@Transf_cat B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t
  T A D h)))
≔ @is_contr_center (@= (Hom (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)) (@comp_fapp0
  (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t
  T A D h) (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)
  (@zero_arrow_family_triangle_to B C C1 t T A D h) (@zero_arrow_family_triangle_from B C C1 t T A D h)) (@id (@Transf_cat B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t
  T A D h)))
   ((@discrete_hom_is_prop (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h))
  D) ((@one_cat_functor_category B (Functor_cat WalkingArrow_cat C) (@one_cat_functor_category
  WalkingArrow_cat C C1)) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t
  T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)) (@comp_fapp0 (@Transf_cat B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_left
  B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@zero_arrow_family_triangle_to B C C1 t T A D h)
  (@zero_arrow_family_triangle_from B C C1 t T A D h)) (@id (@Transf_cat B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func
  B C C1 t T A D h)) D) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h)));

// Retain both modification maps and laws in the original Transf category.
symbol one_cat_zero_arrow_family_triangle_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 : τ (IsoEvidence (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
  (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h))
≔ @iso_evidence_intro (@Transf_cat B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@one_cat_zero_arrow_family_source_func B C C1 t T A D h)) D)
  (@one_cat_zero_arrow_family_triangle_left B C C1 t T A D h) (@one_cat_zero_arrow_family_triangle_right B C C1 t T A D h) (@zero_arrow_family_triangle_to B C C1
  t T A D h) (@zero_arrow_family_triangle_from B C C1 t T A D h)
   (@zero_arrow_family_triangle_left_law B C C1 t T A D h) (@zero_arrow_family_triangle_right_law B C C1 t T A D h);
