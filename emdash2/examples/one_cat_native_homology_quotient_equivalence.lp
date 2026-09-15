/* Actual whole consumers of the original H=Q(β) to K(ḡ) equivalence. */
require open emdash.emdash3_2_one_cat_native_homology_quotient_equivalence;

// The selected left inverse remains the original native cover descent.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D))) ⊢ (@omega_equiv_along_left_inv (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)) ≡
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z);

// The selected right inverse remains the original native cover descent.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D))) ⊢ (@omega_equiv_along_right_inv (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)) ≡
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z);

// The selected inverse retains its whole Hom action.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  (x y : τ (Obj K)) ⊢ (@tapp1_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) x y
  (@omega_equiv_along_left_inv (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z))) ≡ (@tapp1_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) x y
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z));

// Apply left cancellation after an arbitrary whole map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  (J : τ (Functor K C)) (test_map : τ (@Transf K C J (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat K C) J (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@omega_equiv_along_left_inv (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) test_map) (@eq_ap (@Transf K C
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@Transf K C J
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (λ v : τ
  (@Transf K C (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@homology_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))), (@comp_fapp0 (Functor_cat K C) J
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) v test_map)) _ _
  (@omega_equiv_along_left_law (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)))) : τ (@=
  (@Transf K C J (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@comp_fapp0 (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@omega_equiv_along_left_inv (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)) (@comp_fapp0
  (Functor_cat K C) J (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) test_map)) test_map);

// Apply right cancellation after an arbitrary whole map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  (J : τ (Functor K C)) (test_map : τ (@Transf K C J (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))))) ⊢
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) J (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) (@omega_equiv_along_right_inv (Functor_cat K C)
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)) test_map)
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))))
  (@Transf K C J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))),
  (@comp_fapp0 (Functor_cat K C) J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) v
  test_map)) _ _ (@omega_equiv_along_right_law (Functor_cat K C) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)))) : τ (@=
  (@Transf K C J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))) (@comp_fapp0 (Functor_cat K C) J
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) (@comp_fapp0 (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@omega_equiv_along_right_inv (Functor_cat K C) (@homology_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)) test_map))
  test_map);

// Original quotient/cover reconstruction acts on an arbitrary whole map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  (J : τ (Functor K C)) (test_map : τ (@Transf K C J (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) test_map) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))))
  (@Transf K C J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))),
  (@comp_fapp0 (Functor_cat K C) J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) v
  test_map)) _ _ (@one_cat_native_homology_quotient_comparison_reconstruction K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) : τ (@= (@Transf K C J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))))
  (@comp_fapp0 (Functor_cat K C) J (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) (@comp_fapp0 (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) test_map)) (@comp_fapp0 (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) test_map));

// Original quotient/cover reconstruction acts on an arbitrary whole map.
assert [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  (J : τ (Functor K C)) (test_map : τ (@Transf K C J (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B D g)))) ⊢ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) test_map) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@Transf K C J
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (λ v : τ
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))), (@comp_fapp0
  (Functor_cat K C) J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) v test_map)) _ _
  (@one_cat_native_homology_quotient_comparison_inverse_reconstruction K C C1 Prod t Add T0 P Q N A B D f g
  z))) : τ (@= (@Transf K C J (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C Prod t Add) T0 A
  (@transf_arrow_diagram_func K C B D g) f z))) (@comp_fapp0 (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z) (@comp_fapp0
  (Functor_cat K C) J (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B D g))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_projection K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z) test_map)) (@comp_fapp0 (Functor_cat K C) J
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C B D g)) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@kernel_adjunction_family_boundary_diagram_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) test_map));

// A distinct arbitrary map is not selected as the inverse.
assertnot [K C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 A D)))
  (test_map : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)))) ⊢ (@eq_refl (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z)))
  (@one_cat_native_homology_quotient_comparison_inverse K C C1 Prod t Add T0 P Q N A B D f g z)) : τ (@=
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D
  (@one_cat_native_homology_quotient_outgoing K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z))) (@homology_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q A
  (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t (@additive_terminal_object C
  Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))) (@omega_equiv_along_left_inv (Functor_cat K
  C) (@homology_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) T0 P Q A (@transf_arrow_diagram_func K C B D g) (@one_cat_kernel_family_input K C C1 t
  (@additive_terminal_object C Prod t Add) T0 A (@transf_arrow_diagram_func K C B D g) f z))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C A B f)) D (@one_cat_native_homology_quotient_outgoing K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)))
  (@one_cat_native_homology_quotient_comparison K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B D f g z)
  (@one_cat_native_homology_quotient_comparison_equiv K C C1 Prod t Add T0 P Q N A B D f g z)) test_map);
