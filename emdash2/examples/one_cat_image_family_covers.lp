/* The original image inclusion reconstructs the differential, and the same source map cancels. */
require open emdash.emdash3_2_one_cat_image_family_covers;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  (F : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u v : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0
    P Q) F) Y))
  (p : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C F walking_arrow_src) Y) (@comp_fapp0
    (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C F walking_arrow_src) (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) F) Y u
    (@one_cat_image_family_source_transf B C S C1 t T T0 P Q F)) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C F walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) F) Y v (@one_cat_image_family_source_transf B
    C S C1 t T T0 P Q F))))
  ⊢ @one_cat_image_family_source_reflect_path B C S C1 t T T0 P Q N F Y u v p
  : τ(@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0
    P Q) F) Y) u v);

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (F : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  ⊢ @one_cat_image_family_source_factor_path B C S C1 t T T0 P Q F
  : τ(@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C F walking_arrow_src)
    (@diagram_family_at_func B WalkingArrow_cat C F walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
    (@diagram_family_at_func B WalkingArrow_cat C F walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) F) (@diagram_family_at_func B WalkingArrow_cat
    C F walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0
    Q) F)) (@one_cat_image_family_source_transf B C S C1 t T T0 P Q F)) (@diagram_family_transf B
    WalkingArrow_cat C F walking_arrow_src walking_arrow_tgt walking_arrow_generator));
