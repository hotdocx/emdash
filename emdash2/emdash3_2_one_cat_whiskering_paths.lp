/* Compare whole next-Hom actions through the existing rigid Hom owner. */
require open emdash.emdash3_2_one_cat_adjunction_family_views;
require open emdash.emdash3_2_hom_action_factorization_views;

symbol one_cat_whiskering_left_hom_path [A B E C : Cat] (E1 : τ (IsNCat (cat_succ cat_zero) E)) (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  (D : τ (Functor B A)) (V : τ (Functor E C)) (F G : τ (Functor A E))
  : τ (@= (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B
    C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
    G))) (@comp_cat_fapp0 (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B E) (@fapp0 (Functor_cat A E)
    (Functor_cat B E) (@comp_cat_con_func B A E D) F) (@fapp0 (Functor_cat A E) (Functor_cat B E) (@comp_cat_con_func
    B A E D) G)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
    V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) G)) (@fapp1_func (Functor_cat B
    E) (Functor_cat B C) (@comp_cat_cov_func B E C V) (@fapp0 (Functor_cat A E) (Functor_cat B E) (@comp_cat_con_func
    B A E D) F) (@fapp0 (Functor_cat A E) (Functor_cat B E) (@comp_cat_con_func B A E D) G)) (@fapp1_func (Functor_cat
    A E) (Functor_cat B E) (@comp_cat_con_func B A E D) F G)) (@fapp1_func (Functor_cat A E) (Functor_cat B C)
    (@Hom_func Cat_cat A B E C D V) F G))
≔ @eq_refl (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat
  B C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
  G))) (@fapp1_func (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F G);

symbol one_cat_whiskering_right_hom_path [A B E C : Cat] (E1 : τ (IsNCat (cat_succ cat_zero) E)) (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  (D : τ (Functor B A)) (V : τ (Functor E C)) (F G : τ (Functor A E))
  : τ (@= (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B
    C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
    G))) (@comp_cat_fapp0 (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat A E)
    (Functor_cat A C) (@comp_cat_cov_func A E C V) F) (@fapp0 (Functor_cat A E) (Functor_cat A C) (@comp_cat_cov_func
    A E C V) G)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
    V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) G)) (@fapp1_func (Functor_cat A
    C) (Functor_cat B C) (@comp_cat_con_func B A C D) (@fapp0 (Functor_cat A E) (Functor_cat A C) (@comp_cat_cov_func
    A E C V) F) (@fapp0 (Functor_cat A E) (Functor_cat A C) (@comp_cat_cov_func A E C V) G)) (@fapp1_func (Functor_cat
    A E) (Functor_cat A C) (@comp_cat_cov_func A E C V) F G)) (@fapp1_func (Functor_cat A E) (Functor_cat B C)
    (@Hom_func Cat_cat A B E C D V) F G))
≔ @eq_refl (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat
  B C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
  G))) (@fapp1_func (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F G);


// Apply the common whole Hom-action functor to the original transformation.
symbol one_cat_whiskering_native_path [A B E C : Cat] (E1 : τ (IsNCat (cat_succ cat_zero) E)) (C1 : τ (IsNCat (cat_succ
  cat_zero) C))
  (D : τ (Functor B A)) (V : τ (Functor E C)) (F G : τ (Functor A E)) (alpha : τ (@Transf A E F G))
  : τ (@= (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
    F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) G))) (@fapp1_fapp0 (Functor_cat A
    E) (Functor_cat B C) (@comp_cat_fapp0 (Functor_cat A E) (Functor_cat B E) (Functor_cat B C) (@comp_cat_cov_func B
    E C V) (@comp_cat_con_func B A E D)) F G alpha) (@fapp1_fapp0 (Functor_cat A E) (Functor_cat B C) (@comp_cat_fapp0
    (Functor_cat A E) (Functor_cat A C) (Functor_cat B C) (@comp_cat_con_func B A C D) (@comp_cat_cov_func A E C V)) F
    G alpha))
≔ @eq_trans (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
  V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) G))) (@fapp1_fapp0 (Functor_cat A
  E) (Functor_cat B C) (@comp_cat_fapp0 (Functor_cat A E) (Functor_cat B E) (Functor_cat B C) (@comp_cat_cov_func B E
  C V) (@comp_cat_con_func B A E D)) F G alpha) (@fapp1_fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A
  B E C D V) F G alpha) (@fapp1_fapp0 (Functor_cat A E) (Functor_cat B C) (@comp_cat_fapp0 (Functor_cat A E)
  (Functor_cat A C) (Functor_cat B C) (@comp_cat_con_func B A C D) (@comp_cat_cov_func A E C V)) F G alpha)
    (@eq_ap (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat
      B C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
      V) G))) (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
      V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) G))) (λ M : τ (Functor
      (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C)
      (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
      G))), @fapp0 (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B
      C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
      V) G)) M alpha)
      (@comp_cat_fapp0 (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B E) (@fapp0 (Functor_cat A E)
        (Functor_cat B E) (@comp_cat_con_func B A E D) F) (@fapp0 (Functor_cat A E) (Functor_cat B E)
        (@comp_cat_con_func B A E D) G)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C)
        (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
        G)) (@fapp1_func (Functor_cat B E) (Functor_cat B C) (@comp_cat_cov_func B E C V) (@fapp0 (Functor_cat A E)
        (Functor_cat B E) (@comp_cat_con_func B A E D) F) (@fapp0 (Functor_cat A E) (Functor_cat B E)
        (@comp_cat_con_func B A E D) G)) (@fapp1_func (Functor_cat A E) (Functor_cat B E) (@comp_cat_con_func B A E D)
        F G)) (@fapp1_func (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F G)
        (@one_cat_whiskering_left_hom_path A B E C E1 C1 D V F G))
    (@eq_sym (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
      V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) G))) (@fapp1_fapp0
      (Functor_cat A E) (Functor_cat B C) (@comp_cat_fapp0 (Functor_cat A E) (Functor_cat A C) (Functor_cat B C)
      (@comp_cat_con_func B A C D) (@comp_cat_cov_func A E C V)) F G alpha) (@fapp1_fapp0 (Functor_cat A E)
      (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F G alpha)
      (@eq_ap (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E)
        (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func
        Cat_cat A B E C D V) G))) (Obj (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C)
        (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V)
        G))) (λ M : τ (Functor (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E)
        (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func
        Cat_cat A B E C D V) G))), @fapp0 (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat B C) (@fapp0
        (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat
        B C) (@Hom_func Cat_cat A B E C D V) G)) M alpha)
        (@comp_cat_fapp0 (Hom_cat (Functor_cat A E) F G) (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat A E)
          (Functor_cat A C) (@comp_cat_cov_func A E C V) F) (@fapp0 (Functor_cat A E) (Functor_cat A C)
          (@comp_cat_cov_func A E C V) G)) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat A E) (Functor_cat B C)
          (@Hom_func Cat_cat A B E C D V) F) (@fapp0 (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D
          V) G)) (@fapp1_func (Functor_cat A C) (Functor_cat B C) (@comp_cat_con_func B A C D) (@fapp0 (Functor_cat A
          E) (Functor_cat A C) (@comp_cat_cov_func A E C V) F) (@fapp0 (Functor_cat A E) (Functor_cat A C)
          (@comp_cat_cov_func A E C V) G)) (@fapp1_func (Functor_cat A E) (Functor_cat A C) (@comp_cat_cov_func A E C
          V) F G)) (@fapp1_func (Functor_cat A E) (Functor_cat B C) (@Hom_func Cat_cat A B E C D V) F G)
          (@one_cat_whiskering_right_hom_path A B E C E1 C1 D V F G)));

// Cat-specialized views retain raw parent annotations at the actual consumer.
symbol one_cat_whiskering_path [A B E C : Cat] (E1 : τ (IsNCat (cat_succ cat_zero) E)) (C1 : τ (IsNCat
  (cat_succ cat_zero) C))
  (D : τ (Functor B A)) (V : τ (Functor E C)) (F G : τ (Functor A E)) (alpha : τ (@Transf A E F G))
  : τ (@= (@Transf B C (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A E C V F) D) (@comp_cat_fapp0 B A C (@comp_cat_fapp0 A
    E C V G) D)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B E C V (@comp_cat_fapp0 B A E F D) (@comp_cat_fapp0 B A E G
    D)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B A E D F G) alpha)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B A C D
    (@comp_cat_fapp0 A E C V F) (@comp_cat_fapp0 A E C V G)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func A E C V F G)
    alpha)))
≔ @one_cat_whiskering_native_path A B E C E1 C1 D V F G alpha;
