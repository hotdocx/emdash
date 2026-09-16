require open emdash.emdash3_2_one_cat_native_public_pair_exactness;

// The target is the actual native pair with the original public arrows.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
  g c1))) ⊢ (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q)) ≡ A;
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
  g c1))) ⊢ (@fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0
  p q)) ≡ (@walking_arrow_func C B D g);
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
  g c1))) ⊢ (@terminal_arrow_test_incoming C t T A (@walking_arrow_func C B D g) (@tapp0_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (@ZeroArrowCone_cat C t T)
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@zero_arrow_cone_first_func C t
  T)) (@zero_arrow_cone_diagram_func C t T) (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2
  U0 p q) (@zero_arrow_cone_universal_transf C C1 t T))) ≡ f;
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
  g c1))) ⊢ (@terminal_arrow_test_outgoing C (@walking_arrow_func C B D g)) ≡ g;

// Source inverse is the original selected component inverse.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2)) ⊢ (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@native_public_pair_input C S C1 t T a
  d h A B D f g c0 c1 c2 U0 p q) (@zero_arrow_cone_obj C t T a d h) (@omega_equiv_along_left_inv
  (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h) (@native_public_pair_input C S C1 t T a d
  h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t T a d h A B D f g c0 c1 c2 U0 p q)
  (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q U1 U2))) ≡
  (@omega_equiv_along_left_inv C a A c0 U0);
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2)) ⊢ (@tapp0_fapp0
  WalkingArrow_cat C (@walking_arrow_func C B D g) d walking_arrow_src (@fapp1_fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@native_public_pair_input C
  S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@zero_arrow_cone_obj C t T a d h)
  (@omega_equiv_along_left_inv (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t
  T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q
  U1 U2)))) ≡ (@omega_equiv_along_left_inv C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1 U1);
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2)) ⊢ (@tapp0_fapp0
  WalkingArrow_cat C (@walking_arrow_func C B D g) d walking_arrow_tgt (@fapp1_fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@native_public_pair_input C
  S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@zero_arrow_cone_obj C t T a d h)
  (@omega_equiv_along_left_inv (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t
  T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q
  U1 U2)))) ≡ (@omega_equiv_along_left_inv C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2 U2);

// Source inverse is the original selected component inverse.
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2)) ⊢ (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@native_public_pair_input C S C1 t T a
  d h A B D f g c0 c1 c2 U0 p q) (@zero_arrow_cone_obj C t T a d h) (@omega_equiv_along_right_inv
  (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h) (@native_public_pair_input C S C1 t T a d
  h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t T a d h A B D f g c0 c1 c2 U0 p q)
  (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q U1 U2))) ≡
  (@omega_equiv_along_left_inv C a A c0 U0);
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2)) ⊢ (@tapp0_fapp0
  WalkingArrow_cat C (@walking_arrow_func C B D g) d walking_arrow_src (@fapp1_fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@native_public_pair_input C
  S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@zero_arrow_cone_obj C t T a d h)
  (@omega_equiv_along_right_inv (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t
  T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q
  U1 U2)))) ≡ (@omega_equiv_along_left_inv C (@fapp0 WalkingArrow_cat C d walking_arrow_src) B c1 U1);
assert [C : Cat] (S : τ (@PreadditiveCategory C))
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
 (U2 : τ (@OmegaEquivAlong C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2)) ⊢ (@tapp0_fapp0
  WalkingArrow_cat C (@walking_arrow_func C B D g) d walking_arrow_tgt (@fapp1_fapp0 (@ZeroArrowCone_cat C
  t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T) (@native_public_pair_input C
  S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@zero_arrow_cone_obj C t T a d h)
  (@omega_equiv_along_right_inv (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a d h)
  (@native_public_pair_input C S C1 t T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_map C S C1 t
  T a d h A B D f g c0 c1 c2 U0 p q) (@native_public_pair_equiv C S C1 t T a d h A B D f g c0 c1 c2 U0 p q
  U1 U2)))) ≡ (@omega_equiv_along_left_inv C (@fapp0 WalkingArrow_cat C d walking_arrow_tgt) D c2 U2);
