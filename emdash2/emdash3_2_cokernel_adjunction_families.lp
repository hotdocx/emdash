/* Whole cokernel-family mates from the original native adjunction. */
require open emdash.emdash3_2_kernel_cokernel_adjunctions;

// Q applied to a whole diagram family.
symbol cokernel_adjunction_family_func [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (Functor B C)
≔ @comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q) D;

// The counit ε:Q∘I⇒id, prewhiskered by the target family A.
symbol cokernel_adjunction_family_counit_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T)) (A : τ (Functor B C))
  : τ (@Transf B C
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)) A)
≔ @fapp0 _ _ (@comp_cat_con_fapp1_func B C C A
      (@comp_cat_fapp0 C (Functor_cat WalkingArrow_cat C) C
        (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)) (@id_func C))
    (@counit_adj_transf (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T Q) (@initial_arrow_diagram_func C t T)
      (@cokernel_adjunction_evidence C S t T Q));

// Q applied to the original whole cocone h:D⇒I∘A.
symbol cokernel_adjunction_family_action_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (A : τ (Functor B C))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) D
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (@Transf B C (@cokernel_adjunction_family_func B C S t T Q D)
      (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T Q)
        (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
≔ @fapp0 _ _ (@comp_cat_cov_fapp1_func B (Functor_cat WalkingArrow_cat C) C
      (@cokernel_adjunction_func C S t T Q) D
      (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)) h;

// Whole colift = (ε∘A) ∘ Q(h); no ordinary factor record is involved.
symbol cokernel_adjunction_family_colift_transf [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (A : τ (Functor B C))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) D
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) A)))
  : τ (@Transf B C (@cokernel_adjunction_family_func B C S t T Q D) A)
≔ @comp_fapp0 (Functor_cat B C) (@cokernel_adjunction_family_func B C S t T Q D) _ A
    (@cokernel_adjunction_family_counit_transf B C S t T Q A)
    (@cokernel_adjunction_family_action_transf B C S t T Q D A h);
