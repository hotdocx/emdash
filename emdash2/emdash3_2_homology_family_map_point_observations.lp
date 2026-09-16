/* Actual H-map comparison through original whole quotients and native inputs. */
require open emdash.emdash3_2_one_cat_homology_family_maps;
require open emdash.emdash3_2_homology_family_point_paths;
require open emdash.emdash3_2_one_cat_cokernel_point_cancellation;

// Reflect through the original whole-family quotient at its point.
symbol homology_family_point_quotient_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
 (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
 (X : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
 (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) X) D)) (x : τ (Obj B))
 (Target : τ (Obj C)) (u v : τ (Hom C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D
  h) x) Target))
 (w : τ (@= (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) Target) (@comp_fapp0 C
  (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) Target u (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C S t T T0 P Q X D h)
  x (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h))) (@comp_fapp0 C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@homology_adjunction_family_func B C S t
  T T0 P Q X D h) x) Target v (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h)))))
 : τ (@= (Hom C (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) Target) u v)
≔ @one_cat_cokernel_quotient_reflect_path C S C1 t T T0 Q Target (@fapp0 B (Functor_cat WalkingArrow_cat
  C) (@kernel_adjunction_family_boundary_diagram_func B C S t T P X D h) x) u v
 (@eq_trans _ _ _ _
  (@eq_ap (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x)) (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) Target) (λ q : τ (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@homology_adjunction_family_func B C S t
  T T0 P Q X D h) x)), (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x)
  (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) Target u q)) _ _ (@eq_sym _ _ _
  (@cokernel_family_projection_at_path B C S C1 t T0 Q (@kernel_adjunction_family_boundary_diagram_func B
  C S t T P X D h) x)))
  (@eq_trans _ _ _ _ w
   (@eq_ap (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x)) (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) Target) (λ q : τ (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@homology_adjunction_family_func B C S t
  T T0 P Q X D h) x)), (@comp_fapp0 C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x)
  (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h) x) Target v q)) _ _
  (@cokernel_family_projection_at_path B C S C1 t T0 Q (@kernel_adjunction_family_boundary_diagram_func B
  C S t T P X D h) x))));

// Observe the already-proved whole map/quotient equation.
symbol homology_family_map_projection_at_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject
  (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (X Y
  : τ
  (Functor B C)) (D E : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
  C t T)
  X) D)) (k : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) Y) E)) (a : τ (@Transf B C X Y)) (m : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) D E)) (e : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_src)) (@comp_fapp0 (Functor_cat B C) X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@sym_transf_tapp0_transf
  B WalkingArrow_cat C D E m walking_arrow_src) (@zero_arrow_family_incoming_transf B C t T X D h))
  (@comp_fapp0
  (Functor_cat B C) X Y (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)
  (@zero_arrow_family_incoming_transf B C t T Y E k) a))) (x : τ (Obj B))
 : τ (@= (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x)) (@comp_fapp0 C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@homology_adjunction_family_func B C S t
  T T0 P Q X D h) x) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x)
  (@tapp0_fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q X D h)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x (@one_cat_homology_family_map_transf B C S
  C1 t T T0 P Q X Y D E h k a m e)) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q X D h) x
  (@homology_adjunction_family_projection_transf B C S t T T0 P Q X D h))) (@comp_fapp0 C (@fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C (@kernel_adjunction_family_func B C S t T
  P E) x) (@fapp0 B C (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x) (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C S t T P E) (@homology_adjunction_family_func B C S t T T0 P Q Y E k)
  x (@homology_adjunction_family_projection_transf B C S t T T0 P Q Y E k)) (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C S t T P D) (@kernel_adjunction_family_func B C S t T P E) x
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))))
≔ @eq_ap (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B C
  S t T T0 P Q Y E k)) (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C S t T P D) x) (@fapp0 B C
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x))
 (λ w : τ (@Transf B C (@kernel_adjunction_family_func B C S t T P D) (@homology_adjunction_family_func B
  C S t T T0 P Q Y E k)), @tapp0_fapp0 B C (@kernel_adjunction_family_func B C S t T P D)
  (@homology_adjunction_family_func B C S t T T0 P Q Y E k) x w) _ _
 (@one_cat_homology_family_map_projection_path B C S C1 t T T0 P Q X Y D E h k a m e);
