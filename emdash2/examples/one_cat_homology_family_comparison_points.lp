require open emdash.emdash3_2_one_cat_homology_family_comparison_points;
// catalog-area: Whole native homology family comparison

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (Obj B)) ⊢
 @iso_evidence_to C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input B C t T A D h b))
  (@one_cat_homology_family_point_comparison_evidence B C C1 t T A D h S P T0 Q b)
 ≡ @tapp0_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@comp_cat_fapp0 B
  (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h)) b (@iso_evidence_to
  (Functor_cat B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@comp_cat_fapp0 B
  (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (Obj B)) ⊢
 @iso_evidence_from C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input B C t T A D h b))
  (@one_cat_homology_family_point_comparison_evidence B C C1 t T A D h S P T0 Q b)
 ≡ @tapp0_fapp0 B C (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T T0 P Q (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1
  t T A D h)) (@homology_adjunction_family_func B C S t T T0 P Q A D h) b (@iso_evidence_from (Functor_cat
  B C) (@homology_adjunction_family_func B C S t T T0 P Q A D h) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C
  t T) C (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1 t T A D h))
  (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q));

assert [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F G : τ (Functor (Op_cat A) B))
 (eta : τ (@Transf (Op_cat A) B F G)) (x : τ (Obj A)) ⊢
 @one_cat_transf_identity_path (Op_cat A) B B1 F G eta x
 : τ (@= (Hom B (@fapp0 (Op_cat A) B F x) (@fapp0 (Op_cat A) B G x))
     (@tapp1_fapp0 (Op_cat A) B F G x x eta (@id A x))
     (@tapp0_fapp0 (Op_cat A) B F G x eta));

assertnot [A B : Cat] (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F G : τ (Functor (Op_cat A) B))
 (eta : τ (@Transf (Op_cat A) B F G)) (x : τ (Obj A)) (p : τ (Hom A x x)) ⊢
 @one_cat_transf_identity_path (Op_cat A) B B1 F G eta x
 : τ (@= (Hom B (@fapp0 (Op_cat A) B F x) (@fapp0 (Op_cat A) B G x))
     (@tapp1_fapp0 (Op_cat A) B F G x x eta p)
     (@tapp0_fapp0 (Op_cat A) B F G x eta));

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D)) (b : τ (Obj B)) ⊢
 @fapp0 B (@ZeroArrowCone_cat C t T) (@one_cat_zero_arrow_family_func B C C1 t T A D h) b
 ≡ @zero_arrow_family_point_input B C t T A D h b;
