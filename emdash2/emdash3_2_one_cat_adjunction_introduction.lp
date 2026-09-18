/* Ordinary Hom-comparison introduction into the existing Adjunction classifier.
   The input is a whole ProfComparison with selected maps and inverse laws.
   This is one explicit structural constructor, not a derived inhabitant of
   the previously opaque classifier. Seven scoped proof-time views retain the
   native mate and unit/counit runtime heads. Whole η/ε agreement is derived
   through existing mate formulas and ordinary modifications. No caller
   supplies naturality squares; no unrestricted higher interpretation is claimed. */
require open emdash.emdash3_2_one_cat_hom_comparison_data;

// Introduce F⊣G from the original whole Hom comparison, retaining ordinary guards.
injective symbol one_cat_adjunction_from_hom_comparison [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) : τ (@Adjunction A B F G);

// Proof-time input agreement only; preserve the existing runtime cut heads.
unif_rule @Adjunction_hom_prof_comparison _ _ _ _
    (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i) ≡ $other ↪ [ $i ≡ $other ];

// Proof-time input agreement only; preserve the existing runtime cut heads.
unif_rule defiso_to (@Adjunction_hom_prof_comparison _ _ _ _
    (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i)) ≡ $other ↪ [ defiso_to $i ≡ $other ];

// Proof-time input agreement only; preserve the existing runtime cut heads.
unif_rule defiso_from (@Adjunction_hom_prof_comparison _ _ _ _
    (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i)) ≡ $other ↪ [ defiso_from $i ≡ $other ];

// Preserve actual evaluation endpoints in the residual; omitted-RHS reconstruction is unqualified.
unif_rule @tapp0_fapp0 $K $C $P $Q $ab
    (@defiso_to $D $x $y (@Adjunction_hom_prof_comparison _ _ _ _
      (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i))) ≡ $other
  ↪ [ @tapp0_fapp0 $K $C $P $Q $ab (@defiso_to $D $x $y $i) ≡ $other ];

// Preserve actual evaluation endpoints in the residual; omitted-RHS reconstruction is unqualified.
unif_rule @fapp0 $S $T (@tapp0_fapp0 $K $C $P $Q $ab
    (@defiso_to $D $x $y (@Adjunction_hom_prof_comparison _ _ _ _
      (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i)))) $f ≡ $other
  ↪ [ @fapp0 $S $T (@tapp0_fapp0 $K $C $P $Q $ab (@defiso_to $D $x $y $i)) $f ≡ $other ];

// Preserve actual evaluation endpoints in the residual; omitted-RHS reconstruction is unqualified.
unif_rule @tapp0_fapp0 $K $C $P $Q $ab
    (@defiso_from $D $x $y (@Adjunction_hom_prof_comparison _ _ _ _
      (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i))) ≡ $other
  ↪ [ @tapp0_fapp0 $K $C $P $Q $ab (@defiso_from $D $x $y $i) ≡ $other ];

// Preserve actual evaluation endpoints in the residual; omitted-RHS reconstruction is unqualified.
unif_rule @fapp0 $S $T (@tapp0_fapp0 $K $C $P $Q $ab
    (@defiso_from $D $x $y (@Adjunction_hom_prof_comparison _ _ _ _
      (@one_cat_adjunction_from_hom_comparison _ _ _ _ _ _ $i)))) $f ≡ $other
  ↪ [ @fapp0 $S $T (@tapp0_fapp0 $K $C $P $Q $ab (@defiso_from $D $x $y $i)) $f ≡ $other ];

// Stage primary input agreement before specializing the input's head.
symbol one_cat_adjunction_from_hom_comparison_input_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A)) (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@= (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) i)
≔ @eq_refl (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)) (@Adjunction_hom_prof_comparison A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i));

// Match the native unit identity image with the constructed unit component.
protected symbol hom_comparison_adjunction_unit_point_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj A))
 : τ (@= (Obj (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i)))
≔ @eq_trans (Obj (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@fapp0 (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B x (@fapp0 A B F x)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F x))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i))
   (@eq_sym (Obj (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))) (@fapp0 (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B x (@fapp0 A B F x)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F x))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@one_cat_adjunction_unit_identity_image_path A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) x))
   (@eq_sym (Obj (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x)))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i)) (@fapp0 (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F x)) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B x (@fapp0 A B F x)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F x))) (@one_cat_hom_comparison_unit_component_path A B A1 B1 F G i x));

// Whole unit agreement from the already-whole transformations and ordinary component laws.
symbol one_cat_adjunction_from_hom_comparison_unit_modification [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (Hom (@Transf_cat A A (@id_func A) (@comp_cat_fapp0 A B A G F)) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_unit A B A1 B1 F G i))
≔ @one_cat_modification A A A1 (@id_func A) (@comp_cat_fapp0 A B A G F) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_unit A B A1 B1 F G i)
   (λ x : τ (Obj A), @path_to_hom (Hom_cat A x (@fapp0 B A G (@fapp0 A B F x))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i))
      (@hom_comparison_adjunction_unit_point_path A B A1 B1 F G i x));

// Equality observes the same whole unit modification in its discrete category.
symbol one_cat_adjunction_from_hom_comparison_unit_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@= (@Transf A A (@id_func A) (@comp_cat_fapp0 A B A G F)) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_unit A B A1 B1 F G i))
≔ @hom_to_path (@Transf_cat A A (@id_func A) (@comp_cat_fapp0 A B A G F))
   ((@one_cat_functor_category A A A1) (@id_func A) (@comp_cat_fapp0 A B A G F)) (@unit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_unit A B A1 B1 F G i)
   (@one_cat_adjunction_from_hom_comparison_unit_modification A B A1 B1 F G i);

// Match the native counit identity image with the constructed counit component.
protected symbol hom_comparison_adjunction_counit_point_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj B))
 : τ (@= (Obj (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i)))
≔ @eq_trans (Obj (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@fapp0 (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G x) x) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G x))) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i))
   (@eq_sym (Obj (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)) (@fapp0 (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G x) x) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G x))) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@one_cat_adjunction_counit_identity_image_path A B A1 B1 F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i) x))
   (@eq_sym (Obj (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x)) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@fapp0 (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G x)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G x) x) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G x))) (@one_cat_hom_comparison_counit_component_path A B A1 B1 F G i x));

// Whole counit agreement from the already-whole transformations and ordinary component laws.
symbol one_cat_adjunction_from_hom_comparison_counit_modification [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (Hom (@Transf_cat B B (@comp_cat_fapp0 B A B F G) (@id_func B)) (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_counit A B A1 B1 F G i))
≔ @one_cat_modification B B B1 (@comp_cat_fapp0 B A B F G) (@id_func B) (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_counit A B A1 B1 F G i)
   (λ x : τ (Obj B), @path_to_hom (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) x) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i))) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i))
      (@hom_comparison_adjunction_counit_point_path A B A1 B1 F G i x));

// Equality observes the same whole counit modification in its discrete category.
symbol one_cat_adjunction_from_hom_comparison_counit_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@= (@Transf B B (@comp_cat_fapp0 B A B F G) (@id_func B)) (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_counit A B A1 B1 F G i))
≔ @hom_to_path (@Transf_cat B B (@comp_cat_fapp0 B A B F G) (@id_func B))
   ((@one_cat_functor_category B B B1) (@comp_cat_fapp0 B A B F G) (@id_func B)) (@counit_adj_transf A B F G (@one_cat_adjunction_from_hom_comparison A B A1 B1 F G i)) (@one_cat_hom_comparison_counit A B A1 B1 F G i)
   (@one_cat_adjunction_from_hom_comparison_counit_modification A B A1 B1 F G i);
