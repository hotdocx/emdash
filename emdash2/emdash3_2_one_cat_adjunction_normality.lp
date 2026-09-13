/* Fixed-forward normality of the actual whole Coim⇒Im. */
require open emdash.emdash3_2_one_cat_image_coimage_comparison;
require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_iso_evidence_constructors;

// Transparent alias; no unrelated object equivalence can replace the actual map.
symbol OneCatAdjunctionNormality [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) : Grpd
≔ @OmegaEquivAlong (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q);

// Choose the already supplied left inverse, as one whole transformation.
symbol one_cat_coimage_image_inverse_transf [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
≔ @omega_equiv_along_left_inv (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N;

// Whole ordinary iso evidence; both laws are obtained from the same fixed-a data.
symbol one_cat_coimage_image_iso_evidence [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  : τ (IsoEvidence (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
≔ @iso_evidence_intro (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)
    (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)
    (@omega_equiv_along_left_law (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
      (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N)
    (@omega_equiv_left_as_right_law (Functor_cat (Functor_cat WalkingArrow_cat C) C)
      (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
      (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N);

// Restrict the same fixed-a evidence to a whole diagram family by generic action.
symbol one_cat_adjunction_normality_family [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  (F : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  : τ (@OmegaEquivAlong (Functor_cat B C)
      (@fapp0 _ _ (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
        (@adjunction_coimage_func C S t T T0 P Q))
      (@fapp0 _ _ (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
        (@adjunction_image_func C S t T T0 P Q))
      (@fapp1_fapp0 _ _ (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
        (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
        (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
≔ @omega_equiv_along_fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C)
    (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N;
