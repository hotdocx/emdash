/* Actual public pair input and exactness transport; no target-zero or exactness assumption. */
require open emdash.emdash3_2_one_cat_native_pair_comparisons;
require open emdash.emdash3_2_one_cat_pair_comparison_zero;
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;
require open emdash.emdash3_2_one_cat_categorical_exactness_points;

// The source whole input already supplies zero composition.
symbol native_public_pair_zero_path [C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a : τ (Obj C)] (d : τ (Functor WalkingArrow_cat C))
 (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a) d))
 [A B D : τ (Obj C)] (f : τ (Hom C A B)) (g : τ (Hom C B D))
 (c0 : τ (Hom C a A)) (c1 : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B)) (c2 : τ (Hom C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D))
 (U0 : τ (@OmegaEquivAlong C a A c0))
 (p : τ (@= (Hom C a B) (@comp_fapp0 C a (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1
  (@terminal_arrow_test_incoming C t T a d h)) (@comp_fapp0 C a A B f c0)))
 (q : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) D) (@comp_fapp0 C (@fapp0
  WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2
  (@terminal_arrow_test_outgoing C d)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B D
  g c1)))
 : τ (@= (Hom C A D) (@comp_fapp0 C A B D g f) (@preadditive_hom_zero C S A D))
≔ @pair_comparison_zero_path C S a (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0
  WalkingArrow_cat C d walking_arrow_tgt) A B D (@terminal_arrow_test_incoming C t T a d h)
  (@terminal_arrow_test_outgoing C d) f g c0 c1 c2 U0 p q
 (@terminal_arrow_test_chain_path C S t T a d h);

// The public arrows determine their original native zero-cone input.
symbol native_public_pair_input [C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a : τ (Obj C)] (d : τ (Functor WalkingArrow_cat C))
 (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a) d))
 [A B D : τ (Obj C)] (f : τ (Hom C A B)) (g : τ (Hom C B D))
 (c0 : τ (Hom C a A)) (c1 : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B)) (c2 : τ (Hom C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D))
 (U0 : τ (@OmegaEquivAlong C a A c0))
 (p : τ (@= (Hom C a B) (@comp_fapp0 C a (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1
  (@terminal_arrow_test_incoming C t T a d h)) (@comp_fapp0 C a A B f c0)))
 (q : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) D) (@comp_fapp0 C (@fapp0
  WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2
  (@terminal_arrow_test_outgoing C d)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B D
  g c1)))
 : τ (Obj (@ZeroArrowCone_cat C t T))
≔ (@zero_composite_native_cone C S C1 t T A B D f g (@native_public_pair_zero_path C S C1 t T a d h A B D
  f g c0 c1 c2 U0 p q));

symbol native_public_pair_map [C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a : τ (Obj C)] (d : τ (Functor WalkingArrow_cat C))
 (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a) d))
 [A B D : τ (Obj C)] (f : τ (Hom C A B)) (g : τ (Hom C B D))
 (c0 : τ (Hom C a A)) (c1 : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B)) (c2 : τ (Hom C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D))
 (U0 : τ (@OmegaEquivAlong C a A c0))
 (p : τ (@= (Hom C a B) (@comp_fapp0 C a (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1
  (@terminal_arrow_test_incoming C t T a d h)) (@comp_fapp0 C a A B f c0)))
 (q : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) D) (@comp_fapp0 C (@fapp0
  WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2
  (@terminal_arrow_test_outgoing C d)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B D
  g c1)))
 : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h) (@native_public_pair_input C S C1
  t T a d h A B D f g c0 c1 c2 U0 p q))
≔ @native_pair_input_map C S C1 t T a A d (@walking_arrow_func C B D g) h (@terminal_zero_composite_transf
  C S C1 t T A B D f g (@native_public_pair_zero_path C S C1 t T a d h A B D f g c0 c1 c2 U0 p q)) c0 c1
  c2 p q;

// Retain all three selected inverse components.
symbol native_public_pair_equiv [C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a : τ (Obj C)] (d : τ (Functor WalkingArrow_cat C))
 (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a) d))
 [A B D : τ (Obj C)] (f : τ (Hom C A B)) (g : τ (Hom C B D))
 (c0 : τ (Hom C a A)) (c1 : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B)) (c2 : τ (Hom C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D))
 (U0 : τ (@OmegaEquivAlong C a A c0))
 (p : τ (@= (Hom C a B) (@comp_fapp0 C a (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1
  (@terminal_arrow_test_incoming C t T a d h)) (@comp_fapp0 C a A B f c0)))
 (q : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) D) (@comp_fapp0 C (@fapp0
  WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2
  (@terminal_arrow_test_outgoing C d)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B D
  g c1)))
 (U1 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1))
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2))
 : τ (@OmegaEquivAlong (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t
  T a d h A B D f g c0 c1 c2 U0 p q))
≔ @native_pair_input_equiv C S C1 t T a A d (@walking_arrow_func C B D g) h
  (@terminal_zero_composite_transf C S C1 t T A B D f g (@native_public_pair_zero_path C S C1 t T a d h A
  B D f g c0 c1 c2 U0 p q)) c0 c1 c2 p q U0 U1 U2;

// Transport the original canonical comparison witness along the actual input equivalence.
symbol native_public_pair_exact [C : Cat] (S : τ (@PreadditiveCategory C))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a : τ (Obj C)] (d : τ (Functor WalkingArrow_cat C))
 (h : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a) d))
 [A B D : τ (Obj C)] (f : τ (Hom C A B)) (g : τ (Hom C B D))
 (c0 : τ (Hom C a A)) (c1 : τ (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B)) (c2 : τ (Hom C
  (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D))
 (U0 : τ (@OmegaEquivAlong C a A c0))
 (p : τ (@= (Hom C a B) (@comp_fapp0 C a (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1
  (@terminal_arrow_test_incoming C t T a d h)) (@comp_fapp0 C a A B f c0)))
 (q : τ (@= (Hom C (@fapp0 WalkingArrow_cat C d walking_arrow_src) D) (@comp_fapp0 C (@fapp0
  WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2
  (@terminal_arrow_test_outgoing C d)) (@comp_fapp0 C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B D
  g c1)))
 (U1 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1))
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2))
 (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
 (original : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N (@zero_arrow_cone_obj C t T a d h)))
 : τ (@OneCatNativeExactAt C S C1 t T T0 P Q N (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1
  c2 U0 p q))
≔ @one_cat_native_exactness_transport C S C1 t T T0 P Q N (@zero_arrow_cone_obj C t T a d h)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t
  T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q
  U1 U2) original;
