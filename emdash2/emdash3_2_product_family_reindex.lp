require open emdash.emdash3_2_reindex_composition_paths;
require open emdash.emdash3_2_product_family_action_views;

/* Whole paired-functor restriction, retaining each original factor. */

unif_rule @comp_fapp0 Cat_cat $A $B (Product_cat $C $D) (Struct_sigma $F $G) $U
  ≡ @Struct_sigma _ _ $F0 $G0
  ↪ [ $F0 ≡ @comp_fapp0 Cat_cat $A $B $C $F $U;
      $G0 ≡ @comp_fapp0 Cat_cat $A $B $D $G $U ];

// Apply the same postcomposing functor to that literal paired restriction.
// This is sufficient congruence of the existing point owner, not injectivity.
unif_rule @hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $A (Product_cat $C $D) $E $P
    (@comp_fapp0 Cat_cat $A $B (Product_cat $C $D) (Struct_sigma $F $G) $U)
  ≡ @hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $A0 (Product_cat $C0 $D0) $E0 $P0
    (Struct_sigma $F0 $G0)
  ↪ [ $A ≡ $A0; $C ≡ $C0; $D ≡ $D0; $E ≡ $E0; $P ≡ $P0;
      $F0 ≡ @comp_fapp0 Cat_cat $A $B $C $F $U;
      $G0 ≡ @comp_fapp0 Cat_cat $A $B $D $G $U ];

// The original product-mate input retains its diagonal source before restriction.
unif_rule @hom_precomp_along_fapp1_func _ _ (@id Cat_cat Cat_cat) (Product_cat $C $C) $A $B $U
    (@comp_fapp0 Cat_cat $B $C (Product_cat $C $C)
      (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $X)
    (Struct_sigma $F $G)
  ≡ @Product_map_func _ _ _ _ $HC $HD
  ↪ [ $HC ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $C $A $B $U $X $F;
      $HD ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $C $A $B $U $X $G ];

// The coproduct-mate input is the corresponding diagonal-target instance.
unif_rule @hom_precomp_along_fapp1_func _ _ (@id Cat_cat Cat_cat) (Product_cat $C $C) $A $B $U
    (Struct_sigma $F $G)
    (@comp_fapp0 Cat_cat $B $C (Product_cat $C $C)
      (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $Y)
  ≡ @Product_map_func _ _ _ _ $HC $HD
  ↪ [ $HC ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $C $A $B $U $F $Y;
      $HD ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat) $C $A $B $U $G $Y ];

// The raw left-associated presentation of the same restricted product family.
unif_rule @comp_fapp0 Cat_cat $A $B $E
    (@comp_fapp0 Cat_cat $B (Product_cat $C $D) $E $P (Struct_sigma $F $G)) $U
  ≡ @hom_postcomp_fapp0 _ _ (@id Cat_cat Cat_cat) $A0 (Product_cat $C0 $D0) $E0 $P0
    (Struct_sigma $F0 $G0)
  ↪ [ $A ≡ $A0; $C ≡ $C0; $D ≡ $D0; $E ≡ $E0; $P ≡ $P0;
      $F0 ≡ @comp_fapp0 Cat_cat $A $B $C $F $U;
      $G0 ≡ @comp_fapp0 Cat_cat $A $B $D $G $U ];


// Whole projection of a literal paired functor retains its selected coordinate.
unif_rule @comp_fapp0 Cat_cat _ _ _ (@Product_projL_func _ _) (Struct_sigma $F _)
  ≡ $F0 ↪ [ $F ≡ $F0 ];
unif_rule @comp_fapp0 Cat_cat _ _ _ (@Product_projR_func _ _) (Struct_sigma _ $G)
  ≡ $G0 ↪ [ $G ≡ $G0 ];

// Native projection views of the same literal paired restriction.
unif_rule @hom_precomp_along_fapp0 _ _ (@id Cat_cat Cat_cat) _ _ _ (Struct_sigma $F _) (@Product_projL_func _ _)
  ≡ $F0 ↪ [ $F ≡ $F0 ];
unif_rule @hom_precomp_along_fapp0 _ _ (@id Cat_cat Cat_cat) _ _ _ (Struct_sigma _ $G) (@Product_projR_func _ _)
  ≡ $G0 ↪ [ $G ≡ $G0 ];

// A literal paired base retains both native Hom actions at the actual identity target.
unif_rule @hom_precomp_along_fapp1_func _ _ (@id Cat_cat Cat_cat) (Product_cat $C $C) $A _ (Struct_sigma $U0 $U1)
    (@comp_fapp0 Cat_cat _ _ _ (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $X)
    (@id Cat_cat (Product_cat $C $C))
  ≡ @Product_map_func _ _ _ _ $HC $HD
  ↪ [ $HC ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        $C $A (Product_cat $C $C) (Struct_sigma $U0 $U1) $X (@Product_projL_func $C $C);
      $HD ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        $C $A (Product_cat $C $C) (Struct_sigma $U0 $U1) $X (@Product_projR_func $C $C) ];

// The corresponding identity-source restriction keeps the same paired base and incoming legs.
unif_rule @hom_precomp_along_fapp1_func _ _ (@id Cat_cat Cat_cat) (Product_cat $C $C) $A _ (Struct_sigma $U0 $U1)
    (@id Cat_cat (Product_cat $C $C))
    (@comp_fapp0 Cat_cat _ _ _ (Struct_sigma (@id Cat_cat $C) (@id Cat_cat $C)) $Y)
  ≡ @Product_map_func _ _ _ _ $HC $HD
  ↪ [ $HC ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        $C $A (Product_cat $C $C) (Struct_sigma $U0 $U1) (@Product_projL_func $C $C) $Y;
      $HD ≡ @hom_precomp_along_fapp1_func Cat_cat Cat_cat (@id Cat_cat Cat_cat)
        $C $A (Product_cat $C $C) (Struct_sigma $U0 $U1) (@Product_projR_func $C $C) $Y ];

// Whole Hom action at the original diagonal source presentation.
symbol mate_input_source_reindex_hom_path [A B C : Cat] (U : τ (Functor A B)) (X F G : τ (Functor B C))
  : τ (@= (Functor (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (Hom_cat
  (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) U) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) U))) (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@comp_cat_fapp0 B C
  (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) (@Product_map_func (@Transf_cat B C X F) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F
  U)) (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X F) (@comp_cat_con_fapp1_func A B C U X G)))
≔ @eq_refl (Functor (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (Hom_cat
  (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) U) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) U))) (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@comp_cat_fapp0 B C
  (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G));

// The original paired whole input is retained through restriction.
symbol mate_input_source_reindex_path [A B C : Cat] (U : τ (Functor A B)) (X F G : τ (Functor B C))
  (u : τ (@Transf B C X F)) (v : τ (@Transf B C X G))
  : τ (@= (Obj (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C
  (Product_cat C C) (@product_diagonal_func C) X) U) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G) U))) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C))
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) F G)) (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C)
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) U) (@comp_cat_fapp0 A B (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)) (@comp_cat_con_fapp1_func A B
  (Product_cat C C) U (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B
  C X G) u v)) (@Struct_sigma (Obj (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U))) (λ _ : τ
  (Obj (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U))), Obj (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))) (@fapp0 (@Transf_cat B C X F) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@comp_cat_con_fapp1_func A B C U X F) u) (@fapp0
  (@Transf_cat B C X G) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U))
  (@comp_cat_con_fapp1_func A B C U X G) v)))
≔ @eq_ap (Functor (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (Hom_cat
  (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) X) U) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F G) U))) (Obj (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B
  (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) U) (@comp_cat_fapp0 A B
  (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U))) (λ K : τ (Functor
  (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) U)
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U))),
  @fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C)
  X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (Hom_cat (Functor_cat A (Product_cat C
  C)) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) U)
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)) K
  (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) u v))
    (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func
  C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@Product_map_func (@Transf_cat B C X
  F) (@Transf_cat A C (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C F U)) (@Transf_cat B C X G) (@Transf_cat A C
  (@comp_cat_fapp0 A B C X U) (@comp_cat_fapp0 A B C G U)) (@comp_cat_con_fapp1_func A B C U X F)
  (@comp_cat_con_fapp1_func A B C U X G)) (@mate_input_source_reindex_hom_path A B C U X F G);

// Whole Hom action at the original diagonal target presentation.
symbol mate_input_target_reindex_hom_path [A B C : Cat] (U : τ (Functor A B)) (F G Y : τ (Functor B C))
  : τ (@= (Functor (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y)) (Hom_cat (Functor_cat A
  (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) U) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y) U))) (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y))
  (@Product_map_func (@Transf_cat B C F Y) (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U))
  (@Transf_cat B C G Y) (@Transf_cat A C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U))
  (@comp_cat_con_fapp1_func A B C U F Y) (@comp_cat_con_fapp1_func A B C U G Y)))
≔ @eq_refl (Functor (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y)) (Hom_cat (Functor_cat A
  (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) U) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y) U))) (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y));

// The original paired whole input is retained through restriction.
symbol mate_input_target_reindex_path [A B C : Cat] (U : τ (Functor A B)) (F G Y : τ (Functor B C))
  (u : τ (@Transf B C F Y)) (v : τ (@Transf B C G Y))
  : τ (@= (Obj (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B
  C (Product_cat C C) (@product_diagonal_func C) Y) U))) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y)) (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@comp_cat_fapp0 A B (Product_cat C C)
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y) U)) (@comp_cat_con_fapp1_func A B (Product_cat
  C C) U (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y)) (@Struct_sigma (@Transf B C F Y) (λ _ : τ (@Transf B C F Y), @Transf B C G Y) u v))
  (@Struct_sigma (Obj (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U))) (λ _ : τ (Obj
  (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U))), Obj (@Transf_cat A C (@comp_cat_fapp0 A
  B C G U) (@comp_cat_fapp0 A B C Y U))) (@fapp0 (@Transf_cat B C F Y) (@Transf_cat A C (@comp_cat_fapp0 A B C F U)
  (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y) u) (@fapp0 (@Transf_cat B C G Y) (@Transf_cat A
  C (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U G Y) v)))
≔ @eq_ap (Functor (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y)) (Hom_cat (Functor_cat A
  (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) F G) U) (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
  (@product_diagonal_func C) Y) U))) (Obj (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B (Product_cat
  C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@comp_cat_fapp0 A B (Product_cat C
  C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y) U))) (λ K : τ (Functor (Hom_cat (Functor_cat
  B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) (@comp_cat_fapp0 B C
  (Product_cat C C) (@product_diagonal_func C) Y)) (Hom_cat (Functor_cat A (Product_cat C C)) (@comp_cat_fapp0 A B
  (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U) (@comp_cat_fapp0 A B
  (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y) U))), @fapp0 (Hom_cat
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y)) (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) U)
  (@comp_cat_fapp0 A B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y) U)) K
  (@Struct_sigma (@Transf B C F Y) (λ _ : τ (@Transf B C F Y), @Transf B C G Y) u v))
    (@comp_cat_con_fapp1_func A B (Product_cat C C) U (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) F G) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Y)) (@Product_map_func (@Transf_cat B C F
  Y) (@Transf_cat A C (@comp_cat_fapp0 A B C F U) (@comp_cat_fapp0 A B C Y U)) (@Transf_cat B C G Y) (@Transf_cat A C
  (@comp_cat_fapp0 A B C G U) (@comp_cat_fapp0 A B C Y U)) (@comp_cat_con_fapp1_func A B C U F Y)
  (@comp_cat_con_fapp1_func A B C U G Y)) (@mate_input_target_reindex_hom_path A B C U F G Y);
