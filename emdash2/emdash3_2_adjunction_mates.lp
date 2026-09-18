/* Whole adjunction mates; all functors are transparent views of
   existing unit/counit or Adjunction_hom_prof_comparison operations. */
require open emdash.emdash3_2;

// Direct shortcut for the existing Prof→Catd→Functor usability chain.
// The base is reconstructed in a constraint, not a reducible Product LHS guard.
unif_rule @Prof_cat $A $B ≡ @Functor_cat $Base Cat_cat
  ↪ [ $Base ≡ Product_cat (Op_cat $A) $B ];

/* Literal whole mate functors built from product composition and unit/counit. */

symbol adjunction_transpose_semantic_func
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (Functor (Hom_cat L (@fapp0 R L F X) Y)
      (Hom_cat R X (@fapp0 L R G Y)))
≔ @comp_cat_fapp0
    (Hom_cat L (@fapp0 R L F X) Y)
    (Product_cat
      (Hom_cat R X (@fapp0 L R G (@fapp0 R L F X)))
      (Hom_cat R (@fapp0 L R G (@fapp0 R L F X)) (@fapp0 L R G Y)))
    (Hom_cat R X (@fapp0 L R G Y))
    (@comp_prod_func R X (@fapp0 L R G (@fapp0 R L F X)) (@fapp0 L R G Y))
    (Struct_sigma
      (@Const_func (Hom_cat L (@fapp0 R L F X) Y)
        (Hom_cat R X (@fapp0 L R G (@fapp0 R L F X)))
        (@tapp0_fapp0 R R (@id_func R) (@comp_cat_fapp0 R L R G F)
          X (@unit_adj_transf R L F G J)))
      (@fapp1_func L R G (@fapp0 R L F X) Y));

symbol adjunction_untranspose_semantic_func
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (Functor (Hom_cat R X (@fapp0 L R G Y))
      (Hom_cat L (@fapp0 R L F X) Y))
≔ @comp_cat_fapp0
    (Hom_cat R X (@fapp0 L R G Y))
    (Product_cat
      (Hom_cat L (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y)))
      (Hom_cat L (@fapp0 R L F (@fapp0 L R G Y)) Y))
    (Hom_cat L (@fapp0 R L F X) Y)
    (@comp_prod_func L (@fapp0 R L F X) (@fapp0 R L F (@fapp0 L R G Y)) Y)
    (Struct_sigma
      (@fapp1_func R L F X (@fapp0 L R G Y))
      (@Const_func (Hom_cat R X (@fapp0 L R G Y))
        (Hom_cat L (@fapp0 R L F (@fapp0 L R G Y)) Y)
        (@tapp0_fapp0 L L (@comp_cat_fapp0 L R L F G) (@id_func L)
          Y (@counit_adj_transf R L F G J))));

symbol adjunction_hom_component_iso
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (@DefIso Cat_cat (Hom_cat L (@fapp0 R L F X) Y)
      (Hom_cat R X (@fapp0 L R G Y)))
≔ @defiso_fmap
    (Prof_cat R L) Cat_cat
    (@fapp0_func (Product_cat (Op_cat R) L) Cat_cat
      (@Product_pair (Op_cat R) L X Y))
    (@Hom_prof_along R L L F (@id_func L))
    (@Hom_prof_along R L R (@id_func R) G)
    (@Adjunction_hom_prof_comparison R L F G J);

symbol adjunction_transpose_func
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (Functor (Hom_cat L (@fapp0 R L F X) Y)
      (Hom_cat R X (@fapp0 L R G Y)))
≔ @defiso_to Cat_cat (Hom_cat L (@fapp0 R L F X) Y)
    (Hom_cat R X (@fapp0 L R G Y))
    (@adjunction_hom_component_iso R L F G J X Y);

symbol adjunction_untranspose_func
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (Functor (Hom_cat R X (@fapp0 L R G Y))
      (Hom_cat L (@fapp0 R L F X) Y))
≔ @defiso_from Cat_cat (Hom_cat L (@fapp0 R L F X) Y)
    (Hom_cat R X (@fapp0 L R G Y))
    (@adjunction_hom_component_iso R L F G J X Y);

// Projected DefIso cancellation at the existing adjunction comparison.
rule @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_from _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J)))
      (@fapp0 _ _ (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_to _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $h)
  ↪ $h;

rule @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_to _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J)))
      (@fapp0 _ _ (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_from _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $k)
  ↪ $k;

// Capture the actual common category; do not reconstruct its Hom endpoints.
rule @comp_fapp0 Cat_cat $Source _ $Source (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_from _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J))) (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_to _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J)))
  ↪ @id Cat_cat $Source;

rule @comp_fapp0 Cat_cat $Target _ $Target (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_to _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J))) (@tapp0_fapp0 _ _ _ _ $ab
        (@defiso_from _ _ _
          (@Adjunction_hom_prof_comparison $R $L $F $G $J)))
  ↪ @id Cat_cat $Target;

// Whole semantic usability. The selected DefIso component stays the runtime
// owner. Compare with the actual normalized composite, not an alias LHS.
unif_rule
  @tapp0_fapp0 _ _ _ _ (Struct_sigma $X $Y)
    (@defiso_to _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))
  ≡ @comp_fapp0 Cat_cat $Source $Mid $Target $first $second
  ↪ [ (@comp_fapp0 Cat_cat $Source $Mid $Target $first $second)
        ≡ (@adjunction_transpose_semantic_func $R $L $F $G $J $X $Y) ];

unif_rule
  @tapp0_fapp0 _ _ _ _ (Struct_sigma $X $Y)
    (@defiso_from _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))
  ≡ @comp_fapp0 Cat_cat $Source $Mid $Target $first $second
  ↪ [ (@comp_fapp0 Cat_cat $Source $Mid $Target $first $second)
        ≡ (@adjunction_untranspose_semantic_func $R $L $F $G $J $X $Y) ];

// Point-first semantic views of those same whole comparisons.
unif_rule
  @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X $Y)
    (@defiso_to _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $h
  ≡ @comp_fapp0 $C $a $b $c $g $f
  ↪ [ (@comp_fapp0 $C $a $b $c $g $f)
        ≡ (@fapp0 _ _ (@adjunction_transpose_semantic_func $R $L $F $G $J $X $Y) $h) ];

unif_rule
  @fapp0 _ _ (@tapp0_fapp0 _ _ _ _ (Struct_sigma $X $Y)
    (@defiso_from _ _ _ (@Adjunction_hom_prof_comparison $R $L $F $G $J))) $k
  ≡ @comp_fapp0 $C $a $b $c $g $f
  ↪ [ (@comp_fapp0 $C $a $b $c $g $f)
        ≡ (@fapp0 _ _ (@adjunction_untranspose_semantic_func $R $L $F $G $J $X $Y) $k) ];

symbol adjunction_transpose_semantic_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (@= (Functor (Hom_cat L (@fapp0 R L F X) Y) (Hom_cat R X (@fapp0 L R G Y)))
      (@adjunction_transpose_func R L F G J X Y) (@adjunction_transpose_semantic_func R L F G J X Y))
≔ eq_refl (@adjunction_transpose_func R L F G J X Y);

symbol adjunction_untranspose_semantic_path
  [R L : Cat] [F : τ (Functor R L)] [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G)) (X : τ (Obj R)) (Y : τ (Obj L))
  : τ (@= (Functor (Hom_cat R X (@fapp0 L R G Y)) (Hom_cat L (@fapp0 R L F X) Y))
      (@adjunction_untranspose_func R L F G J X Y) (@adjunction_untranspose_semantic_func R L F G J X Y))
≔ eq_refl (@adjunction_untranspose_func R L F G J X Y);

// Native unit component is the identity image under the existing mate comparison.
symbol one_cat_adjunction_unit_identity_image_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (J : τ (@Adjunction A B F G)) (x : τ (Obj A))
 : τ (@= (Obj (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))) (@fapp0 (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))) (@adjunction_transpose_func A B F G J x (@fapp0 A B F x)) (@id B (@fapp0 A B F x))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@unit_adj_transf A B F G J)))
≔ @eq_ap (Functor (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))) (Obj (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))))
   (λ M : τ (Functor (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))), @fapp0 (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))) M (@id B (@fapp0 A B F x)))
   (@adjunction_transpose_func A B F G J x (@fapp0 A B F x)) (@adjunction_transpose_semantic_func A B F G J x (@fapp0 A B F x)) (@adjunction_transpose_semantic_path A B F G J x (@fapp0 A B F x));

// Native counit component is the identity image under the existing mate comparison.
symbol one_cat_adjunction_counit_identity_image_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (J : τ (@Adjunction A B F G)) (x : τ (Obj B))
 : τ (@= (Obj (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)) (@fapp0 (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x) (@adjunction_untranspose_func A B F G J (@fapp0 B A G x) x) (@id A (@fapp0 B A G x))) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@counit_adj_transf A B F G J)))
≔ @eq_ap (Functor (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)) (Obj (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x))
   (λ M : τ (Functor (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)), @fapp0 (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x) M (@id A (@fapp0 B A G x)))
   (@adjunction_untranspose_func A B F G J (@fapp0 B A G x) x) (@adjunction_untranspose_semantic_func A B F G J (@fapp0 B A G x) x) (@adjunction_untranspose_semantic_path A B F G J (@fapp0 B A G x) x);
