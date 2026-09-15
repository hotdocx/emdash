/* Original native annotation fields and inverse choices survive packaging. */
require open emdash.emdash3_2_one_cat_native_exact_tail_observations;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@transf_arrow_diagram_func K C B D g))) (p : τ (@= (@Transf K C A B)
  (@zero_arrow_family_incoming_transf K C t T A (@transf_arrow_diagram_func K C B D g) h) f)) (e : τ
  (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N))
  ⊢ (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g
  (@one_cat_native_exact_arrow_pair_intro K C S C1 t T T0 P Q N A B D f g h p e)) ≡ (@omega_arrow_data
  (Functor_cat K C) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func K C t T A (@transf_arrow_diagram_func K C B D g) h))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_image_to_kernel_transf K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N) e);
assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@transf_arrow_diagram_func K C B D g))) (p : τ (@= (@Transf K C A B)
  (@zero_arrow_family_incoming_transf K C t T A (@transf_arrow_diagram_func K C B D g) h) f)) (e : τ
  (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N))
  ⊢ (@omega_arrow_observation (Functor_cat K C) (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B
  D f g (@one_cat_native_exact_arrow_pair_intro K C S C1 t T T0 P Q N A B D f g h p e))) ≡ (@lax_edge
  (Functor_cat K C) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P
  Q) (@zero_arrow_family_incoming_func K C t T A (@transf_arrow_diagram_func K C B D g) h))
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B D g))
  (@one_cat_image_to_kernel_transf K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N));
assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@transf_arrow_diagram_func K C B D g))) (p : τ (@= (@Transf K C A B)
  (@zero_arrow_family_incoming_transf K C t T A (@transf_arrow_diagram_func K C B D g) h) f)) (e : τ
  (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N))
  ⊢ (@omega_arrow_observation_evidence (Functor_cat K C) (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0
  P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro K C S C1 t T T0 P Q N A B D f g h p e))) ≡ e;
assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@transf_arrow_diagram_func K C B D g))) (p : τ (@= (@Transf K C A B)
  (@zero_arrow_family_incoming_transf K C t T A (@transf_arrow_diagram_func K C B D g) h) f)) (e : τ
  (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N))
  ⊢ (@omega_equiv_along_left_inv (Functor_cat K C) (sigma_Fst (@omega_arrow_observation (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e)))) (sigma_Fst (sigma_Snd (@omega_arrow_observation (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e))))) (sigma_Snd (sigma_Snd (@omega_arrow_observation (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e))))) (@omega_arrow_observation_evidence (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e)))) ≡ (@omega_equiv_along_left_inv (Functor_cat K C) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K
  C t T A (@transf_arrow_diagram_func K C B D g) h)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@one_cat_image_to_kernel_transf K C S C1 t T T0 P Q A
  (@transf_arrow_diagram_func K C B D g) h N) e);
assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B D : τ (Functor K C)] (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
  (h : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) A) (@transf_arrow_diagram_func K C B D g))) (p : τ (@= (@Transf K C A B)
  (@zero_arrow_family_incoming_transf K C t T A (@transf_arrow_diagram_func K C B D g) h) f)) (e : τ
  (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g) h N))
  ⊢ (@omega_equiv_along_right_inv (Functor_cat K C) (sigma_Fst (@omega_arrow_observation (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e)))) (sigma_Fst (sigma_Snd (@omega_arrow_observation (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e))))) (sigma_Snd (sigma_Snd (@omega_arrow_observation (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e))))) (@omega_arrow_observation_evidence (Functor_cat K C)
  (@one_cat_native_exact_arrow_pair_data K C S C1 t T T0 P Q N A B D f g (@one_cat_native_exact_arrow_pair_intro
  K C S C1 t T T0 P Q N A B D f g h p e)))) ≡ (@omega_equiv_along_right_inv (Functor_cat K C) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) (@zero_arrow_family_incoming_func K
  C t T A (@transf_arrow_diagram_func K C B D g) h)) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B D g)) (@one_cat_image_to_kernel_transf K C S C1 t T T0 P Q A
  (@transf_arrow_diagram_func K C B D g) h N) e);
