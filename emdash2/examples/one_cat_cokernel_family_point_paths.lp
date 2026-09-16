/* The actual whole descent may be precomposed after its point comparison. */
require open emdash.emdash3_2_one_cat_cokernel_family_point_paths;

assert [B C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (Y : τ (Functor B C))
  (u : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y))
  (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) Y)
      (@comp_fapp0 (Functor_cat B C)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
        (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) Y u
        (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))
      (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)
        Y)))
 (x : τ (Obj B))
  (W : τ (Obj C)) (before : τ (Hom C W (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S
  t T0 Q) D) x)))
 ⊢ (@eq_ap (Hom C (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  S
  t T0 Q) D) x) (@fapp0 B C Y x)) (Hom C W (@fapp0 B C Y x)) (λ q : τ (Hom C (@fapp0 B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S
  t T0 Q) D) x) (@fapp0 B C Y x)), @comp_fapp0 C W (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@cokernel_adjunction_func C S
  t T0 Q) D) x) (@fapp0 B C Y x) q before) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  C
  (@cokernel_adjunction_func C S t T0 Q) D) Y x (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z))
  (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T0 Q (@fapp0 B C Y x) (@fapp0 B (Functor_cat
  WalkingArrow_cat C) D x)) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) x (@one_cat_cokernel_family_input B C C1 t T T0 D
  Y u z)))
   (@one_cat_cokernel_family_descent_point_path B C S C1 t T T0 Q D Y u z x))
 : τ (@= (Hom C W (@fapp0 B C Y x)) (@comp_fapp0 C W (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S
  t T0 Q) D) x) (@fapp0 B C Y x) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D) Y x (@one_cat_cokernel_family_descent B C S C1 t T T0 Q D Y u z))
  before) (@comp_fapp0 C W (@fapp0 B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S
  t T0 Q) D) x) (@fapp0 B C Y x) (@fapp0 _ _ (@cokernel_adjunction_colift_func C S t T0 Q (@fapp0 B C Y x)
  (@fapp0 B (Functor_cat WalkingArrow_cat C) D x)) (@tapp0_fapp0 B (Functor_cat WalkingArrow_cat C) D
  (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) Y) x (@one_cat_cokernel_family_input B C C1 t T T0 D
  Y u z))) before));
