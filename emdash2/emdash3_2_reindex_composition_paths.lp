require open emdash.emdash3_2_one_cat_whiskering_paths;

/* Native reindexing composition and its retained whole Hom action. */

// The existing Cat composition normal form associates left before comparison.
unif_rule @hom_precomp_along_fapp0 _ _ (@id Cat_cat Cat_cat) $C $A $D
    (@comp_fapp0 Cat_cat $A $B $D $U $V) $F
  ≡ @comp_fapp0 Cat_cat $A $B $C (@comp_fapp0 Cat_cat $B $D $C $F $U) $V
  ↪ [ tt ≡ tt ];

// Stage generic Hom action before concrete precomposition functors accumulate.
symbol functor_hom_comp_path [A B C : Cat]
  (F : τ (Functor A B)) (G : τ (Functor B C)) (x y : τ (Obj A))
  : τ (@= (Functor (Hom_cat A x y) (Hom_cat C (@fapp0 B C G (@fapp0 A B F x)) (@fapp0 B C G (@fapp0 A B F y))))
      (@comp_cat_fapp0 (Hom_cat A x y) (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
        (Hom_cat C (@fapp0 B C G (@fapp0 A B F x)) (@fapp0 B C G (@fapp0 A B F y)))
        (@fapp1_func B C G (@fapp0 A B F x) (@fapp0 A B F y)) (@fapp1_func A B F x y))
      (@fapp1_func A C (@comp_cat_fapp0 A B C G F) x y))
≔ @eq_refl (Functor (Hom_cat A x y) (Hom_cat C (@fapp0 B C G (@fapp0 A B F x)) (@fapp0 B C G (@fapp0 A B F y))))
    (@fapp1_func A C (@comp_cat_fapp0 A B C G F) x y);

symbol prewhisker_native_assoc_hom_path [A B D C : Cat]
  (V : τ (Functor A B)) (U : τ (Functor B D)) (F G : τ (Functor D C))
  : τ (@= (Functor (Hom_cat (Functor_cat D C) F G)
      (Hom_cat (Functor_cat A C)
        (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F)
        (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) G)))
      (@comp_cat_fapp0 (Hom_cat (Functor_cat D C) F G)
        (Hom_cat (Functor_cat B C)
          (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) F)
          (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) G))
        (Hom_cat (Functor_cat A C)
          (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F)
          (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) G))
        (@fapp1_func (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C V)
          (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) F)
          (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) G))
        (@fapp1_func (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) F G))
      (@fapp1_func (Functor_cat D C) (Functor_cat A C)
        (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F G))
≔ @functor_hom_comp_path (Functor_cat D C) (Functor_cat B C) (Functor_cat A C)
    (@comp_cat_con_func B D C U) (@comp_cat_con_func A B C V) F G;

// Apply the checked complete Hom-action comparison at the original whole eta.
symbol prewhisker_native_assoc_path [A B D C : Cat]
  (V : τ (Functor A B)) (U : τ (Functor B D)) (F G : τ (Functor D C)) (eta : τ (@Transf D C F G))
  : τ (@= (Obj (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C
  (@comp_cat_fapp0 A B D U V)) F) (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C
  (@comp_cat_fapp0 A B D U V)) G))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C V)
  (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) F) (@fapp0 (Functor_cat D C) (Functor_cat B
  C) (@comp_cat_con_func B D C U) G) (@fapp1_fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) F
  G eta)) (@fapp1_fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F G
  eta))
≔ @eq_ap (Functor (Hom_cat (Functor_cat D C) F G) (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat D C) (Functor_cat A
  C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F) (@fapp0 (Functor_cat D C) (Functor_cat A C)
  (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) G))) (Obj (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat D
  C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F) (@fapp0 (Functor_cat D C)
  (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) G))) (λ K : τ (Functor (Hom_cat
  (Functor_cat D C) F G) (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A
  D C (@comp_cat_fapp0 A B D U V)) F) (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C
  (@comp_cat_fapp0 A B D U V)) G))), @fapp0 (Hom_cat (Functor_cat D C) F G) (Hom_cat (Functor_cat A C) (@fapp0
  (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F) (@fapp0 (Functor_cat D
  C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) G)) K eta)
    (@comp_cat_fapp0 (Hom_cat (Functor_cat D C) F G) (Hom_cat (Functor_cat B C) (@fapp0 (Functor_cat D C) (Functor_cat
  B C) (@comp_cat_con_func B D C U) F) (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) G))
  (Hom_cat (Functor_cat A C) (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A
  B D U V)) F) (@fapp0 (Functor_cat D C) (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) G))
  (@fapp1_func (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C V) (@fapp0 (Functor_cat D C) (Functor_cat
  B C) (@comp_cat_con_func B D C U) F) (@fapp0 (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) G))
  (@fapp1_func (Functor_cat D C) (Functor_cat B C) (@comp_cat_con_func B D C U) F G)) (@fapp1_func (Functor_cat D C)
  (Functor_cat A C) (@comp_cat_con_func A D C (@comp_cat_fapp0 A B D U V)) F G)
  (@prewhisker_native_assoc_hom_path A B D C V U F G);

/* Composition of whole prewhiskering actions at the original functors. */

symbol prewhisker_assoc_path [A B D C : Cat]
  (V : τ (Functor A B)) (U : τ (Functor B D)) (F G : τ (Functor D C)) (eta : τ (@Transf D C F G))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A D C F (@comp_cat_fapp0 A B D U V))
      (@comp_cat_fapp0 A D C G (@comp_cat_fapp0 A B D U V)))
      (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C V (@comp_cat_fapp0 B D C F U) (@comp_cat_fapp0 B D C G U))
        (@fapp0 _ _ (@comp_cat_con_fapp1_func B D C U F G) eta))
      (@fapp0 _ _ (@comp_cat_con_fapp1_func A D C (@comp_cat_fapp0 A B D U V) F G) eta))
≔ @prewhisker_native_assoc_path A B D C V U F G eta;

symbol prewhisker_identity_path [A B C : Cat]
  (U : τ (Functor A B)) (X : τ (Functor B C))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U))
      (@fapp0 (@Transf_cat B C X X)
        (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C X U))
        (@comp_cat_con_fapp1_func A B C U X X) (@id (Functor_cat B C) X))
      (@id (Functor_cat A C) (@comp_cat_fapp0 A B C X U)))
≔ @fapp1_id_path (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C U) X;

// Generic functoriality of whole restriction, with its ordinary raw parent view.
symbol prewhisker_comp_path [A B C : Cat] (U : τ (Functor A B))
  (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Y)) (g : τ (@Transf B C Y Z))
  : τ (@= (@Transf A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C Z U))
      (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X Z) (@comp_fapp0 (Functor_cat B C) X Y Z g f))
      (@comp_fapp0 (Functor_cat A C) (@comp_cat_fapp0 A B C X U)
        (@comp_cat_fapp0 A B C Y U) (@comp_cat_fapp0 A B C Z U)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U Y Z) g)
        (@fapp0 _ _ (@comp_cat_con_fapp1_func A B C U X Y) f)))
≔ @fapp1_comp_path (Functor_cat B C) (Functor_cat A C) (@comp_cat_con_func A B C U) X Y Z g f;
