/* Fixed-map normality and its whole chosen inverse at actual selections. */
require open emdash.emdash3_2_one_cat_adjunction_normality;

// The ordinary iso view keeps the actual comparison.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ @iso_evidence_to (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_iso_evidence C S C1 t T T0 P Q N) ≡
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q);

// Its inverse is the original selected whole inverse.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ @iso_evidence_from (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_iso_evidence C S C1 t T T0 P Q N) ≡
      (@one_cat_coimage_image_inverse_transf C
    S C1 t T T0 P Q N);

// Selected inverse followed by a has the retained whole identity law.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ @iso_evidence_left (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_iso_evidence C S C1 t T T0 P Q N) : τ (@= (Hom
      (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0
    P Q)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q)
      (@one_cat_coimage_image_inverse_transf C S
    C1 t T T0 P Q N) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@id (Functor_cat (Functor_cat
    WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)));

// The second law uses the same selected inverse.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  ⊢ @iso_evidence_right (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_iso_evidence C S C1 t T T0 P Q N) : τ (@= (Hom
      (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (@adjunction_image_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P
    Q)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_image_func C S t T T0 P Q)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))
      (@id
    (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_image_func C S t T T0 P Q)));

// Evidence for a cannot certify an unrelated whole map.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (b : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)))
  ⊢ N : τ (@OmegaEquivAlong (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
    (@adjunction_image_func C S t T T0 P Q) b);

// The selected inverse is not replaced by an arbitrary inverse-typed map.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (other : τ (@Transf (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q)))
  ⊢ eq_refl (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N) : τ (@= (@Transf (Functor_cat WalkingArrow_cat
    C) C
    (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q))
      (@one_cat_coimage_image_inverse_transf C S
    C1 t T T0 P Q N) other);

// Generic evaluation gives invertibility of the actual component.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (d : τ (Functor WalkingArrow_cat C))
  ⊢ (@omega_equiv_along_fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) C (@fapp0_func (Functor_cat
    WalkingArrow_cat C) C d) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N) : τ (@OmegaEquivAlong C (@fapp0 (Functor_cat
    WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) d) (@fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C S t T T0 P Q) d) (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) d
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)));

// The component inverse is evaluation of the same whole inverse.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (d : τ (Functor WalkingArrow_cat C))
  ⊢ @omega_equiv_along_left_inv C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
    d) (@fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) d) (@tapp0_fapp0
    (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P
    Q) d (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@omega_equiv_along_fapp1_fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) C (@fapp0_func (Functor_cat WalkingArrow_cat C) C d) (@adjunction_coimage_func
    C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) N) ≡
    @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func
    C S t T T0 P Q) d (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N);

// Whole restriction retains the fixed forward transformation.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (B : Cat) (F : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  ⊢ (@one_cat_adjunction_normality_family B C S C1 t T T0 P Q N F) : τ (@OmegaEquivAlong (Functor_cat B C) (@fapp0
    (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B
    C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q))
    (@fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B
    (Functor_cat WalkingArrow_cat C) C F) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0
    P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)));

// Whole restriction obtains its inverse by generic precomposition action.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (B : Cat) (F : τ (Functor B (Functor_cat WalkingArrow_cat
    C)))
  ⊢ @omega_equiv_along_left_inv (Functor_cat B C) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_coimage_func C S t T T0
    P Q)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B
    (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q)) (@fapp1_fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q)
    (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@one_cat_adjunction_normality_family B C S C1 t T T0 P Q N
      F) ≡
    @fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat
    WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q) (@adjunction_coimage_func C S t T T0 P Q)
    (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N);

// The restricted inverse retains its hom action.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (B : Cat) (F : τ (Functor B (Functor_cat WalkingArrow_cat
    C))) (x y : τ (Obj B))
  ⊢ (@tapp1_func B C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B
    (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) x y (@omega_equiv_along_left_inv (Functor_cat B C) (@fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B
    C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q))
    (@fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B
    (Functor_cat WalkingArrow_cat C) C F) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0
    P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@one_cat_adjunction_normality_family B C S C1 t T T0
      P Q N F))) ≡
    (@tapp1_func B C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B
    (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) x y (@fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P
    Q) (@adjunction_coimage_func C S t T T0 P Q) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N)));

// The restricted inverse retains its next action.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (B : Cat) (F : τ (Functor B (Functor_cat WalkingArrow_cat
    C))) (x y : τ (Obj B)) (m n : τ (Hom B x y))
  ⊢ (@fapp1_func (Hom_cat B x y) (Hom_cat C (@fapp0 B C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P
    Q)) x) (@fapp0 B C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func
    B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_coimage_func C S t T T0 P Q)) y)) (@tapp1_func B C (@fapp0
    (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat
    WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) x y (@omega_equiv_along_left_inv (Functor_cat B C) (@fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B
    C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q))
    (@fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B
    (Functor_cat WalkingArrow_cat C) C F) (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0
    P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@one_cat_adjunction_normality_family B C S C1 t T T0
      P Q N F))) m
    n) ≡ (@fapp1_func (Hom_cat B x y) (Hom_cat C (@fapp0 B C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P
    Q)) x) (@fapp0 B C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func
    B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_coimage_func C S t T T0 P Q)) y)) (@tapp1_func B C (@fapp0
    (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat
    WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P Q)) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) C) (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F)
    (@adjunction_coimage_func C S t T T0 P Q)) x y (@fapp1_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (Functor_cat B C) (@comp_cat_con_func B (Functor_cat WalkingArrow_cat C) C F) (@adjunction_image_func C S t T T0 P
    Q) (@adjunction_coimage_func C S t T T0 P Q) (@one_cat_coimage_image_inverse_transf C S C1 t T T0 P Q N))) m n);
