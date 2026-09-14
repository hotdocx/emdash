require open emdash.emdash3_2_reindex_composition_paths;
require open emdash.emdash3_2_adjunction_mates;

/* Same native adjunction mate and same input, with endpoint presentations compared. */

unif_rule @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X $Y)
    (@defiso_to _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $h
  ≡ @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X0 $Y0)
    (@defiso_to _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $h
  ↪ [ $X ≡ $X0; $Y ≡ $Y0 ];
unif_rule @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X $Y)
    (@defiso_from _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $h
  ≡ @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X0 $Y0)
    (@defiso_from _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $h
  ↪ [ $X ≡ $X0; $Y ≡ $Y0 ];

// Restriction commutes with the whole forward mate at the original restricted families.
symbol one_cat_transpose_reindex_path [A B R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat
  (cat_succ cat_zero) L)) [F : τ (Functor R L)] [G : τ (Functor L R)] (J : τ (@Adjunction R L F G)) (U : τ (Functor A
  B)) (X : τ (Functor B R)) (Y : τ (Functor B L)) (h : τ (@Transf B L (@comp_cat_fapp0 B R L F X) Y))
  : τ (@= (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) (@fapp0 (Hom_cat (Functor_cat B L) (@fapp0
  (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) X) Y) (Hom_cat (Functor_cat B R) X (@fapp0
  (Functor_cat B L) (Functor_cat B R) (@comp_cat_cov_func B L R G) Y)) (@one_cat_adjunction_family_transpose_func B R
  L R1 L1 F G J X Y) h)) (@fapp0 (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L)
  (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (Hom_cat (Functor_cat A R)
  (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R) (@comp_cat_cov_func A L R G)
  (@comp_cat_fapp0 A B L Y U))) (@one_cat_adjunction_family_transpose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X
  U) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h)))
≔ (@eq_trans (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (@fapp0 _
  _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) (@fapp0 (Hom_cat (Functor_cat B L) (@fapp0
  (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) X) Y) (Hom_cat (Functor_cat B R) X (@fapp0
  (Functor_cat B L) (Functor_cat B R) (@comp_cat_cov_func B L R G) Y)) (@one_cat_adjunction_family_transpose_func B R
  L R1 L1 F G J X Y) h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) (@comp_fapp0
  (Functor_cat B R) X (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h) (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R X
  (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J)))) (@fapp0 (Hom_cat (Functor_cat A L) (@fapp0
  (Functor_cat A R) (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L
  Y U)) (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R)
  (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U))) (@one_cat_adjunction_family_transpose_func A R L R1 L1 F
  G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U
  (@comp_cat_fapp0 B R L F X) Y) h)) (@eq_ap (@Transf B R X (@comp_cat_fapp0 B L R G Y)) (@Transf A R (@comp_cat_fapp0
  A B R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (λ k : τ (@Transf B R X (@comp_cat_fapp0 B L R G
  Y)), (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) k)) (@fapp0 (Hom_cat (Functor_cat
  B L) (@fapp0 (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) X) Y) (Hom_cat (Functor_cat B R) X
  (@fapp0 (Functor_cat B L) (Functor_cat B R) (@comp_cat_cov_func B L R G) Y))
  (@one_cat_adjunction_family_transpose_func B R L R1 L1 F G J X Y) h) (@comp_fapp0 (Functor_cat B R) X
  (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h) (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R X
  (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J)))
  (@one_cat_adjunction_family_transpose_agrees B R L R1 L1 F G J X Y h)) (@eq_trans (@Transf A R (@comp_cat_fapp0 A B
  R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U X
  (@comp_cat_fapp0 B L R G Y)) (@comp_fapp0 (Functor_cat B R) X (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X))
  (@comp_cat_fapp0 B L R G Y) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h) (@fapp0
  _ _ (@comp_cat_con_fapp1_func B R R X (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J))))
  (@comp_fapp0 (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G
  (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y))
  (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B R R X (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J)))) (@fapp0
  (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0
  A B R X U)) (@comp_cat_fapp0 A B L Y U)) (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat
  A L) (Functor_cat A R) (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U)))
  (@one_cat_adjunction_family_transpose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y
  U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h)) (@prewhisker_comp_path A
  B R U X (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B R R X (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J)) (@fapp0 _
  _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h)) (@eq_trans (@Transf A R (@comp_cat_fapp0 A B
  R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (@comp_fapp0 (Functor_cat A R) (@comp_cat_fapp0 A B R
  X U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R
  (@comp_cat_fapp0 B L R G Y) U) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G
  (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G
  (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G
  (@comp_cat_fapp0 B R L F X))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B R R X (@id_func R) (@comp_cat_fapp0 R L R G
  F)) (@unit_adj_transf R L F G J)))) (@comp_fapp0 (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B
  R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0
  B L R G Y)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A R R (@comp_cat_fapp0 A B R X U) (@id_func R) (@comp_cat_fapp0 R L R G F))
  (@unit_adj_transf R L F G J))) (@fapp0 (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L)
  (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (Hom_cat (Functor_cat A R)
  (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R) (@comp_cat_cov_func A L R G)
  (@comp_cat_fapp0 A B L Y U))) (@one_cat_adjunction_family_transpose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X
  U) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h))
  (@eq_ap (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B
  R L F X)) U)) (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (λ k :
  τ (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F
  X)) U)), (@comp_fapp0 (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G
  (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y))
  (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h)) k)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B R R X (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J))) (@fapp0 _
  _ (@comp_cat_con_fapp1_func A R R (@comp_cat_fapp0 A B R X U) (@id_func R) (@comp_cat_fapp0 R L R G F))
  (@unit_adj_transf R L F G J)) (@prewhisker_assoc_path A B R R U X (@id_func R) (@comp_cat_fapp0 R L R G F)
  (@unit_adj_transf R L F G J))) (@eq_trans (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L R G
  (@comp_cat_fapp0 A B L Y U))) (@comp_fapp0 (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R
  (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0
  B L R G Y)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A R R (@comp_cat_fapp0 A B R X U) (@id_func R) (@comp_cat_fapp0 R L R G F))
  (@unit_adj_transf R L F G J))) (@comp_fapp0 (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R
  (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U)
  (@fapp0 _ _ (@comp_cat_cov_fapp1_func A L R G (@comp_cat_fapp0 A R L F (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0
  A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A R R (@comp_cat_fapp0 A B R X U) (@id_func R) (@comp_cat_fapp0 R L R G F))
  (@unit_adj_transf R L F G J))) (@fapp0 (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L)
  (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (Hom_cat (Functor_cat A R)
  (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R) (@comp_cat_cov_func A L R G)
  (@comp_cat_fapp0 A B L Y U))) (@one_cat_adjunction_family_transpose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X
  U) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h))
  (@eq_ap (@Transf A R (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U)
  (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U)) (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L
  R G (@comp_cat_fapp0 A B L Y U))) (λ k : τ (@Transf A R (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G
  (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U)), (@comp_fapp0 (Functor_cat A
  R) (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U)
  (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G Y) U) k (@fapp0 _ _ (@comp_cat_con_fapp1_func A R R (@comp_cat_fapp0
  A B R X U) (@id_func R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J)))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y))
  (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _
  (@comp_cat_cov_fapp1_func A L R G (@comp_cat_fapp0 A R L F (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U))
  (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h)) (@eq_sym (@Transf A R
  (@comp_cat_fapp0 A B R (@comp_cat_fapp0 B L R G (@comp_cat_fapp0 B R L F X)) U) (@comp_cat_fapp0 A B R
  (@comp_cat_fapp0 B L R G Y) U)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func A L R G (@comp_cat_fapp0 A R L F
  (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U
  (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U (@comp_cat_fapp0 B L R G
  (@comp_cat_fapp0 B R L F X)) (@comp_cat_fapp0 B L R G Y)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B L R G
  (@comp_cat_fapp0 B R L F X) Y) h)) (@one_cat_whiskering_path B A L R L1 R1 U G (@comp_cat_fapp0 B R L F X) Y h)))
  (@eq_sym (@Transf A R (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U))) (@fapp0
  (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0
  A B R X U)) (@comp_cat_fapp0 A B L Y U)) (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat
  A L) (Functor_cat A R) (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U)))
  (@one_cat_adjunction_family_transpose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y
  U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) h)) (@comp_fapp0 (Functor_cat A R)
  (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A R L F (@comp_cat_fapp0 A B R X U)))
  (@comp_cat_fapp0 A L R G (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func A L R G (@comp_cat_fapp0
  A R L F (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U
  (@comp_cat_fapp0 B R L F X) Y) h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A R R (@comp_cat_fapp0 A B R X U) (@id_func
  R) (@comp_cat_fapp0 R L R G F)) (@unit_adj_transf R L F G J))) (@one_cat_adjunction_family_transpose_agrees A R L R1
  L1 F G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y U) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U
  (@comp_cat_fapp0 B R L F X) Y) h)))))));

// Native inverse cuts transfer the same restriction law to the backward mate.
symbol one_cat_untranspose_reindex_path [A B R L : Cat] (R1 : τ (IsNCat (cat_succ cat_zero) R)) (L1 : τ (IsNCat
  (cat_succ cat_zero) L)) [F : τ (Functor R L)] [G : τ (Functor L R)] (J : τ (@Adjunction R L F G)) (U : τ (Functor A
  B)) (X : τ (Functor B R)) (Y : τ (Functor B L)) (k : τ (@Transf B R X (@comp_cat_fapp0 B L R G Y)))
  : τ (@= (@Transf A L (@comp_cat_fapp0 A R L F (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) (@fapp0 (Hom_cat (Functor_cat B R) X (@fapp0
  (Functor_cat B L) (Functor_cat B R) (@comp_cat_cov_func B L R G) Y)) (Hom_cat (Functor_cat B L) (@fapp0 (Functor_cat
  B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) X) Y) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F
  G J X Y) k)) (@fapp0 (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A
  R) (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U))) (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R)
  (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U))
  (@one_cat_adjunction_family_untranspose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y
  U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) k)))
≔ (@eq_ap (Obj (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R)
  (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U)))) (Obj (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A
  R) (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U))) (λ v :
  τ (Obj (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R)
  (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U)))), (@fapp0 (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B
  R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R) (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U)))
  (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0
  A B R X U)) (@comp_cat_fapp0 A B L Y U)) (@one_cat_adjunction_family_untranspose_func A R L R1 L1 F G J
  (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y U)) v)) (@fapp0 (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat
  A R) (Functor_cat A L) (@comp_cat_cov_func A R L F) (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U))
  (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R)
  (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U))) (@one_cat_adjunction_family_transpose_func A R L R1 L1 F
  G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U
  (@comp_cat_fapp0 B R L F X) Y) (@fapp0 (Hom_cat (Functor_cat B R) X (@fapp0 (Functor_cat B L) (Functor_cat B R)
  (@comp_cat_cov_func B L R G) Y)) (Hom_cat (Functor_cat B L) (@fapp0 (Functor_cat B R) (Functor_cat B L)
  (@comp_cat_cov_func B R L F) X) Y) (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J X Y) k))) (@fapp0
  _ _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) k) (@eq_sym (Obj (Hom_cat (Functor_cat A R)
  (@comp_cat_fapp0 A B R X U) (@fapp0 (Functor_cat A L) (Functor_cat A R) (@comp_cat_cov_func A L R G)
  (@comp_cat_fapp0 A B L Y U)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B R U X (@comp_cat_fapp0 B L R G Y)) k)
  (@fapp0 (Hom_cat (Functor_cat A L) (@fapp0 (Functor_cat A R) (Functor_cat A L) (@comp_cat_cov_func A R L F)
  (@comp_cat_fapp0 A B R X U)) (@comp_cat_fapp0 A B L Y U)) (Hom_cat (Functor_cat A R) (@comp_cat_fapp0 A B R X U)
  (@fapp0 (Functor_cat A L) (Functor_cat A R) (@comp_cat_cov_func A L R G) (@comp_cat_fapp0 A B L Y U)))
  (@one_cat_adjunction_family_transpose_func A R L R1 L1 F G J (@comp_cat_fapp0 A B R X U) (@comp_cat_fapp0 A B L Y
  U)) (@fapp0 _ _ (@comp_cat_con_fapp1_func A B L U (@comp_cat_fapp0 B R L F X) Y) (@fapp0 (Hom_cat (Functor_cat B R)
  X (@fapp0 (Functor_cat B L) (Functor_cat B R) (@comp_cat_cov_func B L R G) Y)) (Hom_cat (Functor_cat B L) (@fapp0
  (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) X) Y) (@one_cat_adjunction_family_untranspose_func
  B R L R1 L1 F G J X Y) k))) (@one_cat_transpose_reindex_path A B R L R1 L1 F G J U X Y (@fapp0 (Hom_cat
  (Functor_cat B R) X (@fapp0 (Functor_cat B L) (Functor_cat B R) (@comp_cat_cov_func B L R G) Y)) (Hom_cat
  (Functor_cat B L) (@fapp0 (Functor_cat B R) (Functor_cat B L) (@comp_cat_cov_func B R L F) X) Y)
  (@one_cat_adjunction_family_untranspose_func B R L R1 L1 F G J X Y) k))));
