/* Evaluation of the original whole H comparison at its existing point input.
   This view is downstream of the whole construction and retains its maps. */

require open emdash.emdash3_2_one_cat_homology_family_comparison;

require open emdash.emdash3_2_zero_arrow_family_point_inputs;

// Evaluate that same whole isomorphism at the original point input.
symbol one_cat_homology_family_point_comparison_evidence [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (t : τ (Obj C)) (T : τ (@TerminalObject C t)) (A : τ (Functor B C))
 (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
   (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
     (@terminal_arrow_diagram_func C t T) A) D))
 (S : τ (@PreadditiveCategory C)) (P : τ (@KernelAdjunctionStructure C S t T))
 (T0 : τ (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (Obj B))
 : τ (IsoEvidence C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q A D h) b) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_universal_transf C C1 t T)) (@zero_arrow_family_point_input B C t T A D h b)))
≔ @iso_evidence_fmap (Functor_cat B C) C (@fapp0_func B C b) (@homology_adjunction_family_func B C S t T
  T0 P Q A D h) (@comp_cat_fapp0 B (@ZeroArrowCone_cat C t T) C (@homology_adjunction_family_func
  (@ZeroArrowCone_cat C t T) C S t T T0 P Q (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)) (@one_cat_zero_arrow_family_func B C C1
  t T A D h)) (@one_cat_homology_family_comparison_evidence B C C1 t T A D h S P T0 Q);
