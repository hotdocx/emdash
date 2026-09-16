/* Ordinary reflection for the original native input category.
   No external tuple classifier or specialized identity/composition rule. */
require open emdash.emdash3_2_zero_arrow_cone_maps;
require open emdash.emdash3_2_prop_fibre_constructor_paths;
require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_one_cat_adjunction_families;
require open emdash.emdash3_2_zero_arrow_cone_chain_pairs;

// OneCat makes the remaining native compatibility cell proposition-valued.
symbol zero_cone_map_filler_is_prop [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t))
 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)] [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d1)]
 (u : τ (Hom C a0 a1)) (v : τ (@Transf WalkingArrow_cat C d0 d1))
 : τ (IsPropGrpd (Hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat
  C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 v h0) (@comp_fapp0
  (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t
  T) a0) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u))))
≔ @discrete_hom_is_prop (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat
  WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1)
   ((@one_cat_functor_category WalkingArrow_cat C C1) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 v h0) (@comp_fapp0
  (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t
  T) a0) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u));


// Constructor congruence stays in the actual native Hom.
symbol one_cat_zero_cone_constructed_map_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 [t : τ (Obj C)] (T : τ (@TerminalObject C t)) [a0 a1 : τ (Obj C)]
 [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)] [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d1)]
 [u u1 : τ (Hom C a0 a1)] [v v1 : τ (@Transf WalkingArrow_cat C d0 d1)]
 (alpha : τ (Hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 v h0) (@comp_fapp0
  (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t
  T) a0) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0
  C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u)))) (beta : τ (Hom
  (Hom_cat
  (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t
  T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d0 d1 v1 h0) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) (@fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1 (@fapp1_fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u1))))
 (p : τ (@= (Hom C a0 a1) u u1)) (q : τ (@= (@Transf WalkingArrow_cat C d0 d1) v v1))
 : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1)) (@zero_cone_native_map C t T a0 a1 d0 d1 h0 h1 u v alpha) (@zero_cone_native_map C t T a0 a1 d0
  d1 h0 h1
  u1 v1 beta))
≔ @two_prop_fibre_image_path (Hom C a0 a1) (@Transf WalkingArrow_cat C d0 d1)
   (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1
  d1 h1))
   (λ u0 : τ (Hom C a0 a1), λ v0 : τ (@Transf WalkingArrow_cat C d0 d1), (Hom (Hom_cat (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  a0) d1)
  (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d0 d1 v0 h0) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) (@fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1 (@fapp1_fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u0))))
   (λ u0 : τ (Hom C a0 a1), λ v0 : τ (@Transf WalkingArrow_cat C d0 d1), λ e : τ (Hom (Hom_cat
  (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  a0) d1)
  (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d0 d1 v0 h0) (@comp_fapp0 (Functor_cat WalkingArrow_cat C)
  (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) (@fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1 (@fapp1_fapp0 C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 u0))), (@zero_cone_native_map C t T a0
  a1 d0 d1
  h0 h1 u0 v0 e))
   (@zero_cone_map_filler_is_prop C C1 t T a0 a1 d0 d1 h0 h1) u v alpha u1 v1 beta p q;

// Recover the compatibility cell from the existing whole universal transfor.
symbol one_cat_zero_cone_map_rebuild [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ
  (@TerminalObject C t))
 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)] [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d1)] (m : τ (Hom (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1))) : τ (Hom (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj
  C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1))
≔ (@zero_cone_native_map C t T a0 a1 d0 d1 h0 h1 (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1
  h1) m) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1) m) (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat
  C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) h0) (@comp_fapp0
  (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  a0)
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 (@fapp1_fapp0
  (@ZeroArrowCone_cat
  C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T
  a1 d1 h1) m))) (@zero_arrow_cone_map_naturality C C1 t T (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m)));

// Native Hom elimination and ordinary filler uniqueness recover the original map.
symbol one_cat_zero_cone_map_rebuild_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj
  C)] (T :
  τ (@TerminalObject C t))
 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)] [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d1)] (m : τ (Hom (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1)))
 : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1)) (@one_cat_zero_cone_map_rebuild C C1 t T a0 a1 d0 d1 h0 h1 m) m)
≔ @sigma_ind _ _ (λ q : τ (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1)), @= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T
  a0 d0
  h0) (@zero_arrow_cone_obj C t T a1 d1 h1)) (@one_cat_zero_cone_map_rebuild C C1 t T a0 a1 d0 d1 h0 h1
  q) q)
   (λ u : τ _, λ rest : τ _,
     @sigma_ind _ _ (λ r : τ _, @= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1)) (@one_cat_zero_cone_map_rebuild C C1 t T a0 a1 d0 d1 h0 h1
  (Struct_sigma u r)) (Struct_sigma u r))
       (λ v : τ _, λ alpha : τ _, (@one_cat_zero_cone_constructed_map_path C C1 t T a0 a1 d0 d1 h0 h1 u
  u v v
  (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) (Struct_sigma u
  (Struct_sigma v
  alpha))) h0) (@comp_fapp0 (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  a0)
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 (@fapp1_fapp0
  (@ZeroArrowCone_cat
  C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T
  a1 d1 h1) (Struct_sigma u (Struct_sigma v alpha))))) (@zero_arrow_cone_map_naturality C C1 t T
  (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) (Struct_sigma u (Struct_sigma v alpha)))) alpha (@eq_refl (Hom C
  a0 a1)
  u) (@eq_refl (@Transf WalkingArrow_cat C d0 d1) v))) rest) m;

// The two existing projection functors jointly reflect equality of native maps.
symbol one_cat_zero_cone_map_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T :
  τ
  (@TerminalObject C t))
 [a0 a1 : τ (Obj C)] [d0 d1 : τ (Functor WalkingArrow_cat C)]
 [h0 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C
  t T) a0) d0)] [h1 : τ (@Transf WalkingArrow_cat C (@fapp0 C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a1) d1)] (m n : τ (Hom (@ZeroArrowCone_cat C t T)
  (@zero_arrow_cone_obj C
  t
  T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1)))
 (p : τ (@= (Hom C a0 a1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1
  h1) m) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1
  h1) n)))
 (q : τ (@= (@Transf WalkingArrow_cat C d0 d1) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat
  WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1) m) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1) n)))
 : τ (@= (Hom (@ZeroArrowCone_cat C t T) (@zero_arrow_cone_obj C t
  T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1)) m n)
≔ @eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_zero_cone_map_rebuild_path C C1 t T a0 a1 d0 d1 h0 h1 m))
  (@eq_trans _ _ _ _
    (@one_cat_zero_cone_constructed_map_path C C1 t T a0 a1 d0 d1 h0 h1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T)
  C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1
  h1) m) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T
  a1 d1
  h1) n) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1) m) (@fapp1_fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t
  T a1 d1
  h1) n) (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat
  C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) m) h0) (@comp_fapp0
  (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  a0)
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 (@fapp1_fapp0
  (@ZeroArrowCone_cat
  C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T
  a1 d1 h1) m))) (@zero_arrow_cone_map_naturality C C1 t T (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) m)) (@path_to_hom (Hom_cat (Functor_cat WalkingArrow_cat C)
  (@fapp0 C
  (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) a0) d1) (@comp_fapp0 (Functor_cat WalkingArrow_cat C) (@fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0) d0 d1 (@fapp1_fapp0
  (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C) (@zero_arrow_cone_diagram_func C t T)
  (@zero_arrow_cone_obj C t T a0 d0 h0) (@zero_arrow_cone_obj C t T a1 d1 h1) n) h0) (@comp_fapp0
  (Functor_cat
  WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  a0)
  (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a1) d1 h1
  (@fapp1_fapp0 C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) a0 a1 (@fapp1_fapp0
  (@ZeroArrowCone_cat
  C t T) C (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T
  a1 d1 h1) n))) (@zero_arrow_cone_map_naturality C C1 t T (@zero_arrow_cone_obj C t T a0 d0 h0)
  (@zero_arrow_cone_obj C t T a1 d1 h1) n)) p q)
    (@one_cat_zero_cone_map_rebuild_path C C1 t T a0 a1 d0 d1 h0 h1 n));
