/* Stage whole-family input recovery before specializing model presentations. */
require open emdash.emdash3_2_one_cat_native_public_pair_exactness;
require open emdash.emdash3_2_one_cat_kernel_family_point_paths;
require open emdash.emdash3_2_one_cat_zero_family_paths;

symbol native_family_public_pair_input [K C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 (T0 : τ (@TerminalObject (Op_cat C) t))
 (A B D : τ (Functor K C)) (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
 (zero : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf
  K C t T T0 A D)))
 (x : τ (Obj K)) [A1 B1 D1 : τ (Obj C)]
 (f1 : τ (Hom C A1 B1)) (g1 : τ (Hom C B1 D1))
 (c0 : τ (Hom C (@fapp0 K C A x) A1)) (c1 : τ (Hom C (@fapp0 K C B x) B1)) (c2 : τ (Hom C (@fapp0 K C D x)
  D1))
 (U0 : τ (@OmegaEquivAlong C (@fapp0 K C A x) A1 c0))
 (p : τ (@= (Hom C (@fapp0 K C A x) B1) (@comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C B x) B1 c1
  (@tapp0_fapp0 K C A B x f)) (@comp_fapp0 C (@fapp0 K C A x) A1 B1 f1 c0)))
 (q : τ (@= (Hom C (@fapp0 K C B x) D1) (@comp_fapp0 C (@fapp0 K C B x) (@fapp0 K C D x) D1 c2
  (@tapp0_fapp0 K C B D x g)) (@comp_fapp0 C (@fapp0 K C B x) B1 D1 g1 c1)))
≔ @native_public_pair_input C S C1 t T (@fapp0 K C A x) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C B D g) x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
  (@transf_arrow_diagram_func K C B D g) x (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f zero)) A1 B1 D1 f1 g1 c0 c1 c2 U0 (@eq_trans _ _ _ _ (@eq_ap
  (Hom C (@fapp0 K C A x) (@fapp0 K C B x)) (Hom C (@fapp0 K C A x) B1) (λ e : τ (Hom C (@fapp0 K C A x)
  (@fapp0 K C B x)), (@comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C B x) B1 c1 e)) _ _
  (@one_cat_kernel_family_point_incoming_path K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f
  zero x)) p) q;

symbol native_family_public_pair_equiv [K C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 (T0 : τ (@TerminalObject (Op_cat C) t))
 (A B D : τ (Functor K C)) (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
 (zero : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf
  K C t T T0 A D)))
 (x : τ (Obj K)) [A1 B1 D1 : τ (Obj C)]
 (f1 : τ (Hom C A1 B1)) (g1 : τ (Hom C B1 D1))
 (c0 : τ (Hom C (@fapp0 K C A x) A1)) (c1 : τ (Hom C (@fapp0 K C B x) B1)) (c2 : τ (Hom C (@fapp0 K C D x)
  D1))
 (U0 : τ (@OmegaEquivAlong C (@fapp0 K C A x) A1 c0))
 (p : τ (@= (Hom C (@fapp0 K C A x) B1) (@comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C B x) B1 c1
  (@tapp0_fapp0 K C A B x f)) (@comp_fapp0 C (@fapp0 K C A x) A1 B1 f1 c0)))
 (q : τ (@= (Hom C (@fapp0 K C B x) D1) (@comp_fapp0 C (@fapp0 K C B x) (@fapp0 K C D x) D1 c2
  (@tapp0_fapp0 K C B D x g)) (@comp_fapp0 C (@fapp0 K C B x) B1 D1 g1 c1)))
 (U1 : τ (@OmegaEquivAlong C (@fapp0 K C B x) B1 c1)) (U2 : τ (@OmegaEquivAlong C (@fapp0 K C D x) D1 c2))
≔ @native_public_pair_equiv C S C1 t T (@fapp0 K C A x) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C B D g) x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
  (@transf_arrow_diagram_func K C B D g) x (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f zero)) A1 B1 D1 f1 g1 c0 c1 c2 U0 (@eq_trans _ _ _ _ (@eq_ap
  (Hom C (@fapp0 K C A x) (@fapp0 K C B x)) (Hom C (@fapp0 K C A x) B1) (λ e : τ (Hom C (@fapp0 K C A x)
  (@fapp0 K C B x)), (@comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C B x) B1 c1 e)) _ _
  (@one_cat_kernel_family_point_incoming_path K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f
  zero x)) p) q U1 U2;

symbol native_family_public_pair_exact [K C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 (T0 : τ (@TerminalObject (Op_cat C) t))
 (A B D : τ (Functor K C)) (f : τ (@Transf K C A B)) (g : τ (@Transf K C B D))
 (zero : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A B D g f) (@zero_arrow_family_zero_transf
  K C t T T0 A D)))
 (x : τ (Obj K)) [A1 B1 D1 : τ (Obj C)]
 (f1 : τ (Hom C A1 B1)) (g1 : τ (Hom C B1 D1))
 (c0 : τ (Hom C (@fapp0 K C A x) A1)) (c1 : τ (Hom C (@fapp0 K C B x) B1)) (c2 : τ (Hom C (@fapp0 K C D x)
  D1))
 (U0 : τ (@OmegaEquivAlong C (@fapp0 K C A x) A1 c0))
 (p : τ (@= (Hom C (@fapp0 K C A x) B1) (@comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C B x) B1 c1
  (@tapp0_fapp0 K C A B x f)) (@comp_fapp0 C (@fapp0 K C A x) A1 B1 f1 c0)))
 (q : τ (@= (Hom C (@fapp0 K C B x) D1) (@comp_fapp0 C (@fapp0 K C B x) (@fapp0 K C D x) D1 c2
  (@tapp0_fapp0 K C B D x g)) (@comp_fapp0 C (@fapp0 K C B x) B1 D1 g1 c1)))
 (U1 : τ (@OmegaEquivAlong C (@fapp0 K C B x) B1 c1)) (U2 : τ (@OmegaEquivAlong C (@fapp0 K C D x) D1 c2))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (original : τ (@OneCatAdjunctionExactFamily K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f zero) N))
≔ @native_public_pair_exact C S C1 t T (@fapp0 K C A x) (@fapp0 K (Functor_cat WalkingArrow_cat C)
  (@transf_arrow_diagram_func K C B D g) x) (@tapp0_fapp0 K (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 K C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
  (@transf_arrow_diagram_func K C B D g) x (@one_cat_kernel_family_input K C C1 t T T0 A
  (@transf_arrow_diagram_func K C B D g) f zero)) A1 B1 D1 f1 g1 c0 c1 c2 U0 (@eq_trans _ _ _ _ (@eq_ap
  (Hom C (@fapp0 K C A x) (@fapp0 K C B x)) (Hom C (@fapp0 K C A x) B1) (λ e : τ (Hom C (@fapp0 K C A x)
  (@fapp0 K C B x)), (@comp_fapp0 C (@fapp0 K C A x) (@fapp0 K C B x) B1 c1 e)) _ _
  (@one_cat_kernel_family_point_incoming_path K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f
  zero x)) p) q U1 U2 T0 P Q N
 (@one_cat_exact_family_at K C S C1 t T T0 P Q A (@transf_arrow_diagram_func K C B D g)
  (@one_cat_kernel_family_input K C C1 t T T0 A (@transf_arrow_diagram_func K C B D g) f zero) N x
  original);
