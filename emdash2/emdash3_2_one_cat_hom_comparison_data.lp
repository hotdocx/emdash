/* Whole unit/counit data extracted from a supplied natural Hom comparison.
   All symbols are definitions. The original F/G, comparison and inverse are
   retained; callers supply no naturality squares. Whole triangle laws use
   the existing ordinary modification interface. This does not introduce an
   Adjunction witness or claim an unrestricted higher normalization theorem. */
require open emdash.emdash3_2_represented_comma_families;
require open emdash.emdash3_2_one_cat_arrow_diagrams;
require open emdash.emdash3_2_adjunction_mates;
require open emdash.emdash3_2_eq1_hom_action;
require open emdash.emdash3_2_one_cat_modifications;

// Reconstruct F⇒G from its whole internal Hom action using the shared graph.
symbol one_cat_transf_from_hom_action [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor B C)) (alpha : τ (@Transf (Op_cat B) (@Catd_cat B)
    (@hom_int B B (@id_func B))
    (@comp_cat_fapp0 (Op_cat B) (Op_cat C) (@Catd_cat B)
      (@hom_int C B G) (@Op_func B C F))))
 : τ (@Transf B C F G)
≔ @comp_fapp0 (Functor_cat B C) F (@represented_comma_hom_action_target_func B C C (@id_func C) F G alpha) G (@one_cat_represented_comma_hom_action_target_to B C C (@id_func C) F G alpha C1)
    (@comp_fapp0 (Functor_cat B C) F (@represented_comma_hom_action_source_func B C C (@id_func C) F G alpha) (@represented_comma_hom_action_target_func B C C (@id_func C) F G alpha)
      (@transf_prewhisker B (@LaxArrow_cat C) C (@represented_comma_hom_action_func B C C (@id_func C) F G alpha)
        (@cubical_src_func C) (@cubical_tgt_func C)
        (@one_cat_arrow_universal_transf C C1))
      (@iso_evidence_from (Functor_cat B C) (@represented_comma_hom_action_source_func B C C (@id_func C) F G alpha) F (@represented_comma_hom_action_source_evidence B C C (@id_func C) F G alpha)));

// The original forward comparison, reindexed after the whole action of F.
symbol hom_comparison_unit_profmap [A B : Cat]
  (F : τ (Functor A B)) (G : τ (Functor B A))
  (i : τ (@ProfComparison A B
    (@Hom_prof_along A B B F (@id_func B))
    (@Hom_prof_along A B A (@id_func A) G)))
  : τ (@ProfMap A A (@Unit_prof A)
    (@Hom_prof_along A A A (@id_func A) (@comp_cat_fapp0 A B A G F)))
≔ @comp_catd_fapp0 (Product_cat (Op_cat A) A) (@Unit_prof A)
    (@Hom_prof_along A A B F F)
    (@Hom_prof_along A A A (@id_func A) (@comp_cat_fapp0 A B A G F))
    (@Prof_reindex_transf A A B A
      (@Hom_prof_along A B B F (@id_func B))
      (@Hom_prof_along A B A (@id_func A) G)
      (@defiso_to (Prof_cat A B) _ _ i) (@id_func A) F)
    (@Prof_func_hom A B F);

// The same selected inverse comparison, reindexed after the whole action of G.
symbol hom_comparison_counit_profmap [A B : Cat]
  (F : τ (Functor A B)) (G : τ (Functor B A))
  (i : τ (@ProfComparison A B
    (@Hom_prof_along A B B F (@id_func B))
    (@Hom_prof_along A B A (@id_func A) G)))
  : τ (@ProfMap B B (@Unit_prof B)
    (@Hom_prof_along B B B (@comp_cat_fapp0 B A B F G) (@id_func B)))
≔ @comp_catd_fapp0 (Product_cat (Op_cat B) B) (@Unit_prof B)
    (@Hom_prof_along B B A G G)
    (@Hom_prof_along B B B (@comp_cat_fapp0 B A B F G) (@id_func B))
    (@Prof_reindex_transf A B B B
      (@Hom_prof_along A B A (@id_func A) G)
      (@Hom_prof_along A B B F (@id_func B))
      (@defiso_from (Prof_cat A B) _ _ i) G (@id_func B))
    (@Prof_func_hom B A G);

// Curry the supplied whole represented map at its original hom_int owners.
symbol profmap_internal_hom_action [I C : Cat] (F G : τ (Functor I C))
 (r : τ (@ProfMap I I (@Unit_prof I) (@Hom_prof_along I I C F G)))
 : τ (@Transf (Op_cat I) (@Catd_cat I) (@hom_int I I (@id_func I))
     (@comp_cat_fapp0 (Op_cat I) (Op_cat C) (@Catd_cat I)
       (@hom_int C I G) (@Op_func I C F)))
≔ @fapp1_fapp0 (Functor_cat (Product_cat (Op_cat I) I) Cat_cat)
    (Functor_cat (Op_cat I) (Functor_cat I Cat_cat))
    (@curry_func_func (Op_cat I) I Cat_cat) (@Unit_prof I) (@Hom_prof_along I I C F G) r;

// η:id_A⇒GF, constructed from the identity images of the original comparison.
symbol one_cat_hom_comparison_unit [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@Transf A A (@id_func A) (@comp_cat_fapp0 A B A G F))
≔ @one_cat_transf_from_hom_action A A A1 (@id_func A) (@comp_cat_fapp0 A B A G F) (@profmap_internal_hom_action A A (@id_func A) (@comp_cat_fapp0 A B A G F) (@hom_comparison_unit_profmap A B F G i));

// ε:FG⇒id_B, constructed using the original selected inverse.
symbol one_cat_hom_comparison_counit [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@Transf B B (@comp_cat_fapp0 B A B F G) (@id_func B))
≔ @one_cat_transf_from_hom_action B B B1 (@comp_cat_fapp0 B A B F G) (@id_func B) (@profmap_internal_hom_action B B (@comp_cat_fapp0 B A B F G) (@id_func B) (@hom_comparison_counit_profmap A B F G i));

// Two evaluations preserve the product-pair telescope identity by existing functor laws.
protected symbol hom_comparison_pair_tele_identity_path [A B : Cat] (x : τ (Obj A)) (y : τ (Obj B))
 : τ (@= (Hom (Product_cat A B) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y)) (@tapp0_fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y (@tapp0_fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) (@Product_pair_tele_func A B) x (@id (Functor_cat A (Functor_cat B (Product_cat A B))) (@Product_pair_tele_func A B)))) (@id (Product_cat A B) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y)))
≔ @eq_trans (Hom (Product_cat A B) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y)) (@tapp0_fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y (@tapp0_fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) (@Product_pair_tele_func A B) x (@id (Functor_cat A (Functor_cat B (Product_cat A B))) (@Product_pair_tele_func A B)))) (@tapp0_fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y (@id (Functor_cat B (Product_cat A B)) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x))) (@id (Product_cat A B) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y))
   (@eq_ap (Hom (Functor_cat B (Product_cat A B)) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x)) (Hom (Product_cat A B) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y) (@fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y))
     (λ e : τ (Hom (Functor_cat B (Product_cat A B)) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x)), @tapp0_fapp0 B (Product_cat A B) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x) y e)
     (@tapp0_fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) (@Product_pair_tele_func A B) x (@id (Functor_cat A (Functor_cat B (Product_cat A B))) (@Product_pair_tele_func A B))) (@id (Functor_cat B (Product_cat A B)) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x)) (@fapp1_id_path (Functor_cat A (Functor_cat B (Product_cat A B))) (Functor_cat B (Product_cat A B)) (@fapp0_func A (Functor_cat B (Product_cat A B)) x) (@Product_pair_tele_func A B)))
   (@fapp1_id_path (Functor_cat B (Product_cat A B)) (Product_cat A B) (@fapp0_func B (Product_cat A B) y) (@fapp0 A (Functor_cat B (Product_cat A B)) (@Product_pair_tele_func A B) x));

// Stage transfor identity evaluation before specializing the source product.
protected symbol hom_comparison_transf_identity_beta [A B : Cat]
 (F G : τ (Functor A B)) (r : τ (@Transf A B F G)) (x : τ (Obj A))
 : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B G x))
   (@tapp1_fapp0 A B F G x x r (@id A x)) (@tapp0_fapp0 A B F G x r))
≔ @eq_refl (Hom B (@fapp0 A B F x) (@fapp0 A B G x)) (@tapp0_fapp0 A B F G x r);

// The curried native Hom action retains the original profunctor component.
protected symbol hom_comparison_prof_hom_action_component_path [I C : Cat]
 (I1 : τ (IsNCat (cat_succ cat_zero) I)) (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor I C)) (r : τ (@ProfMap I I (@Unit_prof I) (@Hom_prof_along I I C F G))) (x : τ (Obj I))
 : τ (@= (Functor (Hom_cat I x x) (Hom_cat C (@fapp0 I C F x) (@fapp0 I C G x))) (@tapp0_fapp0 I Cat_cat (@hom_ I I (@id_func I) x)
   (@hom_ C I G (@fapp0 I C F x)) x
   (@tapp0_fapp0 (Op_cat I) (@Catd_cat I) (@hom_int I I (@id_func I))
     (@comp_cat_fapp0 (Op_cat I) (Op_cat C) (@Catd_cat I)
       (@hom_int C I G) (@Op_func I C F)) x (@profmap_internal_hom_action I C F G r))) (@tapp0_fapp0 (Product_cat (Op_cat I) I) Cat_cat (@Unit_prof I) (@Hom_prof_along I I C F G) (@Product_pair (Op_cat I) I x x) r))
≔ @eq_trans (Functor (Hom_cat I x x) (Hom_cat C (@fapp0 I C F x) (@fapp0 I C G x))) (@tapp1_fapp0 (Product_cat (Op_cat I) I) Cat_cat (@Unit_prof I) (@Hom_prof_along I I C F G) (@Product_pair (Op_cat I) I x x) (@Product_pair (Op_cat I) I x x) r (@tapp0_fapp0 I (Product_cat (Op_cat I) I) (@fapp0 (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I)) (@Product_pair_tele_func (Op_cat I) I) x) (@fapp0 (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I)) (@Product_pair_tele_func (Op_cat I) I) x) x (@tapp0_fapp0 (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I)) (@Product_pair_tele_func (Op_cat I) I) (@Product_pair_tele_func (Op_cat I) I) x (@id (Functor_cat (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I))) (@Product_pair_tele_func (Op_cat I) I))))) (@tapp1_fapp0 (Product_cat (Op_cat I) I) Cat_cat (@Unit_prof I) (@Hom_prof_along I I C F G) (@Product_pair (Op_cat I) I x x) (@Product_pair (Op_cat I) I x x) r (@id (Product_cat (Op_cat I) I) (@Product_pair (Op_cat I) I x x))) (@tapp0_fapp0 (Product_cat (Op_cat I) I) Cat_cat (@Unit_prof I) (@Hom_prof_along I I C F G) (@Product_pair (Op_cat I) I x x) r)
   (@eq_ap (Hom (Product_cat (Op_cat I) I) (@Product_pair (Op_cat I) I x x) (@Product_pair (Op_cat I) I x x)) (Functor (Hom_cat I x x) (Hom_cat C (@fapp0 I C F x) (@fapp0 I C G x)))
     (λ p : τ (Hom (Product_cat (Op_cat I) I) (@Product_pair (Op_cat I) I x x) (@Product_pair (Op_cat I) I x x)), @tapp1_fapp0 (Product_cat (Op_cat I) I) Cat_cat (@Unit_prof I) (@Hom_prof_along I I C F G) (@Product_pair (Op_cat I) I x x) (@Product_pair (Op_cat I) I x x) r p)
     (@tapp0_fapp0 I (Product_cat (Op_cat I) I) (@fapp0 (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I)) (@Product_pair_tele_func (Op_cat I) I) x) (@fapp0 (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I)) (@Product_pair_tele_func (Op_cat I) I) x) x (@tapp0_fapp0 (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I)) (@Product_pair_tele_func (Op_cat I) I) (@Product_pair_tele_func (Op_cat I) I) x (@id (Functor_cat (Op_cat I) (Functor_cat I (Product_cat (Op_cat I) I))) (@Product_pair_tele_func (Op_cat I) I)))) (@id (Product_cat (Op_cat I) I) (@Product_pair (Op_cat I) I x x)) (@hom_comparison_pair_tele_identity_path (Op_cat I) I x x))
   (@hom_comparison_transf_identity_beta (Product_cat (Op_cat I) I) Cat_cat (@Unit_prof I) (@Hom_prof_along I I C F G) r (@Product_pair (Op_cat I) I x x));

// Ordinary law η_a=Φ_a,Fa(id_Fa); no operational term is path-transported.
symbol one_cat_hom_comparison_unit_component_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj A))
 : τ (@= (Hom A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) x)) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) x (@one_cat_hom_comparison_unit A B A1 B1 F G i)) (@fapp0 _ _ (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B x (@fapp0 A B F x)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F x))))
≔ @eq_ap (Functor (Hom_cat A x x) (Hom_cat A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) x))) (Hom A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) x))
   (λ q : τ (Functor (Hom_cat A x x) (Hom_cat A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) x))), @fapp0 (Hom_cat A x x) (Hom_cat A (@fapp0 A A (@id_func A) x) (@fapp0 A A (@comp_cat_fapp0 A B A G F) x)) q (@id A x))
   (@tapp0_fapp0 A Cat_cat (@hom_ A A (@id_func A) x)
   (@hom_ A A (@comp_cat_fapp0 A B A G F) (@fapp0 A A (@id_func A) x)) x
   (@tapp0_fapp0 (Op_cat A) (@Catd_cat A) (@hom_int A A (@id_func A))
     (@comp_cat_fapp0 (Op_cat A) (Op_cat A) (@Catd_cat A)
       (@hom_int A A (@comp_cat_fapp0 A B A G F)) (@Op_func A A (@id_func A))) x (@profmap_internal_hom_action A A (@id_func A) (@comp_cat_fapp0 A B A G F) (@hom_comparison_unit_profmap A B F G i)))) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A A (@id_func A) (@comp_cat_fapp0 A B A G F)) (@Product_pair (Op_cat A) A x x) (@hom_comparison_unit_profmap A B F G i)) (@hom_comparison_prof_hom_action_component_path A A A1 A1 (@id_func A) (@comp_cat_fapp0 A B A G F) (@hom_comparison_unit_profmap A B F G i) x);

// Ordinary law ε_b=Φ⁻¹_Gb,b(id_Gb), retaining the actual whole ε.
symbol one_cat_hom_comparison_counit_component_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (x : τ (Obj B))
 : τ (@= (Hom B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) x)) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) x (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@fapp0 _ _ (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G x) x) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G x))))
≔ @eq_ap (Functor (Hom_cat B x x) (Hom_cat B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) x))) (Hom B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) x))
   (λ q : τ (Functor (Hom_cat B x x) (Hom_cat B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) x))), @fapp0 (Hom_cat B x x) (Hom_cat B (@fapp0 B B (@comp_cat_fapp0 B A B F G) x) (@fapp0 B B (@id_func B) x)) q (@id B x))
   (@tapp0_fapp0 B Cat_cat (@hom_ B B (@id_func B) x)
   (@hom_ B B (@id_func B) (@fapp0 B B (@comp_cat_fapp0 B A B F G) x)) x
   (@tapp0_fapp0 (Op_cat B) (@Catd_cat B) (@hom_int B B (@id_func B))
     (@comp_cat_fapp0 (Op_cat B) (Op_cat B) (@Catd_cat B)
       (@hom_int B B (@id_func B)) (@Op_func B B (@comp_cat_fapp0 B A B F G))) x (@profmap_internal_hom_action B B (@comp_cat_fapp0 B A B F G) (@id_func B) (@hom_comparison_counit_profmap A B F G i)))) (@tapp0_fapp0 (Product_cat (Op_cat B) B) Cat_cat (@Unit_prof B) (@Hom_prof_along B B B (@comp_cat_fapp0 B A B F G) (@id_func B)) (@Product_pair (Op_cat B) B x x) (@hom_comparison_counit_profmap A B F G i)) (@hom_comparison_prof_hom_action_component_path B B B1 B1 (@comp_cat_fapp0 B A B F G) (@id_func B) (@hom_comparison_counit_profmap A B F G i) x);

// Project the original displayed naturality cell over (id_x,f).
protected symbol hom_comparison_prof_cov_cell [A C : Cat] (F G : τ (Functor A C))
 (r : τ (@ProfMap A A (@Unit_prof A) (@Hom_prof_along A A C F G)))
 (x y : τ (Obj A)) (f : τ (Hom A x y))
 : τ (Hom (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y))
   (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y)
     (@fapp1_fapp0 A C G x y f)
     (@fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x))
       (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
         (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@id A x)))
   (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y))
     (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
       (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) (@Hom_fapp0 A x x x y (@id A x) f (@id A x))))
≔ @fdapp1_int_cell (Product_cat (Op_cat A) A) (@Unit_prof A)
    (@Hom_prof_along A A C F G) r
    (@Product_pair (Op_cat A) A x x) (@Product_pair (Op_cat A) A x y)
    (@Product_pair (Hom_cat (Op_cat A) x x) (Hom_cat A x y) (@id A x) f)
    (@id A x);

// Stage the rigid Hom/postcomposition comparison before identity specialization.
protected symbol hom_comparison_hom_post_view [A : Cat] (x y z : τ (Obj A))
 (f : τ (Hom A y z)) (h : τ (Hom A x y))
 : τ (@= (Hom A x z) (@Hom_fapp0 A x x y z (@id A x) f h)
     (@comp_fapp0 A x y z f h))
≔ @eq_refl (Hom A x z) (@comp_fapp0 A x y z f h);

// Hom_A(id_x,f)(id_x)=f, as an ordinary observation of existing cuts.
protected symbol hom_comparison_source_id_path [A : Cat] (x y : τ (Obj A)) (f : τ (Hom A x y))
 : τ (@= (Hom A x y) (@Hom_fapp0 A x x x y (@id A x) f (@id A x)) f)
≔ @hom_comparison_hom_post_view A x x y f (@id A x);

// Ordinary covariance: G[f]∘r_x,x(id_x)=r_x,y(f).
protected symbol hom_comparison_prof_cov_path [A C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor A C))
 (r : τ (@ProfMap A A (@Unit_prof A) (@Hom_prof_along A A C F G)))
 (x y : τ (Obj A)) (f : τ (Hom A x y))
 : τ (@= (Hom C (@fapp0 A C F x) (@fapp0 A C G y))
   (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y)
     (@fapp1_fapp0 A C G x y f)
     (@fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x))
       (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
         (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@id A x)))
   (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y))
     (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
       (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) f))
≔ @eq_trans (Hom C (@fapp0 A C F x) (@fapp0 A C G y))
  (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y)
     (@fapp1_fapp0 A C G x y f)
     (@fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x))
       (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
         (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@id A x))) (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
       (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) (@Hom_fapp0 A x x x y (@id A x) f (@id A x))) (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
       (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) f)
  (@hom_to_path (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y))
    (C1 (@fapp0 A C F x) (@fapp0 A C G y)) _ _ (@hom_comparison_prof_cov_cell A C F G r x y f))
  (@eq_ap (Hom A x y) (Hom C (@fapp0 A C F x) (@fapp0 A C G y))
    (λ q : τ (Hom A x y), (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A)
       (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) q)) (@Hom_fapp0 A x x x y (@id A x) f (@id A x)) f (@hom_comparison_source_id_path A x y f));

// Stage the existing naturality cut at generic composable arrows.
protected symbol hom_comparison_transf_post_comp_path [A C : Cat]
 (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor A C)) (eta : τ (@Transf A C F G))
 (x y z : τ (Obj A)) (g : τ (Hom A y z)) (f : τ (Hom A x y))
 : τ (@= (Hom C (@fapp0 A C F x) (@fapp0 A C G z))
   (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G y) (@fapp0 A C G z)
     (@fapp1_fapp0 A C G y z g) (@tapp1_fapp0 A C F G x y eta f))
   (@tapp1_fapp0 A C F G x z eta (@comp_fapp0 A x y z g f)))
≔ @eq_refl (Hom C (@fapp0 A C F x) (@fapp0 A C G z))
   (@tapp1_fapp0 A C F G x z eta (@comp_fapp0 A x y z g f));

// The ordinary transfor cut gives G[f]∘α_x=α[f].
protected symbol hom_comparison_transf_post_path [A C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
 (F G : τ (Functor A C)) (eta : τ (@Transf A C F G))
 (x y : τ (Obj A)) (f : τ (Hom A x y))
 : τ (@= (Hom C (@fapp0 A C F x) (@fapp0 A C G y))
   (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y)
     (@fapp1_fapp0 A C G x y f) (@tapp0_fapp0 A C F G x eta))
   (@tapp1_fapp0 A C F G x y eta f))
≔ @hom_comparison_transf_post_comp_path A C C1 F G eta x x y f (@id A x);

// The reconstructed component is the original identity image r_x,x(id_x).
protected symbol hom_comparison_reconstruction_component_path [A C : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) (F G : τ (Functor A C))
 (r : τ (@ProfMap A A (@Unit_prof A) (@Hom_prof_along A A C F G))) (x : τ (Obj A))
 : τ (@= (Hom C (@fapp0 A C F x) (@fapp0 A C G x)) (@tapp0_fapp0 A C F G x (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r))) (@fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@id A x)))
≔ @eq_ap (Functor (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x))) (Hom C (@fapp0 A C F x) (@fapp0 A C G x))
   (λ p : τ (Functor (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x))),
      @fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x)) p (@id A x))
   (@tapp0_fapp0 A Cat_cat (@hom_ A A (@id_func A) x)
   (@hom_ C A G (@fapp0 A C F x)) x
   (@tapp0_fapp0 (Op_cat A) (@Catd_cat A) (@hom_int A A (@id_func A))
     (@comp_cat_fapp0 (Op_cat A) (Op_cat C) (@Catd_cat A)
       (@hom_int C A G) (@Op_func A C F)) x (@profmap_internal_hom_action A C F G r))) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@hom_comparison_prof_hom_action_component_path A C A1 C1 F G r x);

// The reconstructed whole α retains the original nonidentity action: α[f]=r_x,y(f).
symbol one_cat_profmap_reconstruction_action_path [A C : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (C1 : τ (IsNCat (cat_succ cat_zero) C)) (F G : τ (Functor A C))
 (r : τ (@ProfMap A A (@Unit_prof A) (@Hom_prof_along A A C F G)))
 (x y : τ (Obj A)) (f : τ (Hom A x y))
 : τ (@= (Hom C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp1_fapp0 A C F G x y (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)) f) (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) f))
≔ @eq_trans (Hom C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp1_fapp0 A C F G x y (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)) f) (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y) (@fapp1_fapp0 A C G x y f) (@tapp0_fapp0 A C F G x (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)))) (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) f)
   (@eq_sym (Hom C (@fapp0 A C F x) (@fapp0 A C G y)) (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y) (@fapp1_fapp0 A C G x y f) (@tapp0_fapp0 A C F G x (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)))) (@tapp1_fapp0 A C F G x y (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)) f) (@hom_comparison_transf_post_path A C C1 F G (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)) x y f))
   (@eq_trans (Hom C (@fapp0 A C F x) (@fapp0 A C G y)) (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y) (@fapp1_fapp0 A C G x y f) (@tapp0_fapp0 A C F G x (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r)))) (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y) (@fapp1_fapp0 A C G x y f) (@fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@id A x))) (@fapp0 (Hom_cat A x y) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G y)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x y) r) f)
     (@eq_ap (Hom C (@fapp0 A C F x) (@fapp0 A C G x)) (Hom C (@fapp0 A C F x) (@fapp0 A C G y))
       (λ h : τ (Hom C (@fapp0 A C F x) (@fapp0 A C G x)), (@comp_fapp0 C (@fapp0 A C F x) (@fapp0 A C G x) (@fapp0 A C G y) (@fapp1_fapp0 A C G x y f) h)) (@tapp0_fapp0 A C F G x (@one_cat_transf_from_hom_action A C C1 F G (@profmap_internal_hom_action A C F G r))) (@fapp0 (Hom_cat A x x) (Hom_cat C (@fapp0 A C F x) (@fapp0 A C G x)) (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat (@Unit_prof A) (@Hom_prof_along A A C F G) (@Product_pair (Op_cat A) A x x) r) (@id A x))
       (@hom_comparison_reconstruction_component_path A C A1 C1 F G r x))
     (@hom_comparison_prof_cov_path A C C1 F G r x y f));

// Stage evaluation of a composite before choosing inverse functors.
protected symbol hom_comparison_eval_comp_path [X Y Z : Cat]
 (G : τ (Functor Y Z)) (F : τ (Functor X Y)) (x : τ (Obj X))
 : τ (@= (Obj Z) (@fapp0 X Z (@comp_cat_fapp0 X Y Z G F) x)
     (@fapp0 Y Z G (@fapp0 X Y F x)))
≔ @eq_refl (Obj Z) (@fapp0 Y Z G (@fapp0 X Y F x));

// Observe the original selected left inverse at an object.
protected symbol hom_comparison_defiso_point_left [X Y : Cat] (i : τ (@DefIso Cat_cat X Y)) (x : τ (Obj X))
 : τ (@= (Obj X)
   (@fapp0 Y X (@defiso_from Cat_cat X Y i) (@fapp0 X Y (@defiso_to Cat_cat X Y i) x)) x)
≔ @eq_sym (Obj X) x
   (@fapp0 Y X (@defiso_from Cat_cat X Y i) (@fapp0 X Y (@defiso_to Cat_cat X Y i) x))
   (@hom_comparison_eval_comp_path X Y X (@defiso_from Cat_cat X Y i) (@defiso_to Cat_cat X Y i) x);

// Observe the original selected right inverse at an object.
protected symbol hom_comparison_defiso_point_right [X Y : Cat] (i : τ (@DefIso Cat_cat X Y)) (y : τ (Obj Y))
 : τ (@= (Obj Y)
   (@fapp0 X Y (@defiso_to Cat_cat X Y i) (@fapp0 Y X (@defiso_from Cat_cat X Y i) y)) y)
≔ @eq_sym (Obj Y) y
   (@fapp0 X Y (@defiso_to Cat_cat X Y i) (@fapp0 Y X (@defiso_from Cat_cat X Y i) y))
   (@hom_comparison_eval_comp_path Y X Y (@defiso_to Cat_cat X Y i) (@defiso_from Cat_cat X Y i) y);

// Evaluate the supplied whole DefIso at the original pair (a,b).
protected symbol hom_comparison_prof_component_defiso [A B : Cat] (P Q : τ (Prof A B))
 (i : τ (@ProfComparison A B P Q)) (a : τ (Obj A)) (b : τ (Obj B))
 : τ (@DefIso Cat_cat (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)))
≔ (@defiso_fmap (Prof_cat A B) Cat_cat (@fapp0_func (Product_cat (Op_cat A) B) Cat_cat (@Product_pair (Op_cat A) B a b)) P Q i);

// Retain the supplied comparison in its left component inverse law.
protected symbol hom_comparison_prof_component_left [A B : Cat] (P Q : τ (Prof A B))
 (i : τ (@ProfComparison A B P Q)) (a : τ (Obj A)) (b : τ (Obj B)) (x : τ (Obj (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b))))
 : τ (@= (Obj (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b))) (@fapp0 (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat Q P (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) P Q i)) (@fapp0 (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat P Q (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) P Q i)) x)) x)
≔ @hom_comparison_defiso_point_left (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)) (@hom_comparison_prof_component_defiso A B P Q i a b) x;

// Retain the supplied comparison in its right component inverse law.
protected symbol hom_comparison_prof_component_right [A B : Cat] (P Q : τ (Prof A B))
 (i : τ (@ProfComparison A B P Q)) (a : τ (Obj A)) (b : τ (Obj B)) (x : τ (Obj (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b))))
 : τ (@= (Obj (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b))) (@fapp0 (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat P Q (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) P Q i)) (@fapp0 (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat Q P (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) P Q i)) x)) x)
≔ @hom_comparison_defiso_point_right (@fapp0 (Product_cat (Op_cat A) B) Cat_cat P (@Product_pair (Op_cat A) B a b)) (@fapp0 (Product_cat (Op_cat A) B) Cat_cat Q (@Product_pair (Op_cat A) B a b)) (@hom_comparison_prof_component_defiso A B P Q i a b) x;

// Stage the rigid Hom/precomposition comparison before identity specialization.
protected symbol hom_comparison_hom_pre_view [A : Cat] (x x0 y : τ (Obj A))
 (g : τ (Hom A x0 x)) (h : τ (Hom A x y))
 : τ (@= (Hom A x0 y) (@Hom_fapp0 A x x0 y y g (@id A y) h)
     (@comp_fapp0 A x0 x y h g))
≔ @eq_refl (Hom A x0 y) (@comp_fapp0 A x0 x y h g);

// Hom_A(g,id_y)(id_y)=g, through the existing Hom action.
protected symbol hom_comparison_target_id_path [A : Cat] (x y : τ (Obj A)) (g : τ (Hom A x y))
 : τ (@= (Hom A x y) (@Hom_fapp0 A y x y y g (@id A y) (@id A y)) g)
≔ @hom_comparison_hom_pre_view A y x y g (@id A y);

// Forward mate formula from the original whole comparison’s native naturality.
protected symbol hom_comparison_mate_to_formula [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B))
 (f : τ (Hom B (@fapp0 A B F a) b))
 : τ (@= (Hom A a (@fapp0 B A G b)) (@comp_fapp0 A a (@fapp0 B A G (@fapp0 A B F a)) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F a) b f) (@fapp0 (Hom_cat B (@fapp0 A B F a) (@fapp0 A B F a)) (Hom_cat A a (@fapp0 B A G (@fapp0 A B F a))) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a (@fapp0 A B F a)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F a)))) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) f))
≔ @eq_trans (Hom A a (@fapp0 B A G b)) (@comp_fapp0 A a (@fapp0 B A G (@fapp0 A B F a)) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F a) b f) (@fapp0 (Hom_cat B (@fapp0 A B F a) (@fapp0 A B F a)) (Hom_cat A a (@fapp0 B A G (@fapp0 A B F a))) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a (@fapp0 A B F a)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F a)))) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@Hom_fapp0 B (@fapp0 A B F a) (@fapp0 A B F a) (@fapp0 A B F a) b (@id B (@fapp0 A B F a)) f (@id B (@fapp0 A B F a)))) (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) f)
   (@hom_to_path (Hom_cat A a (@fapp0 B A G b)) (A1 a (@fapp0 B A G b)) _ _ (@fdapp1_int_cell (Product_cat (Op_cat A) B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i) (@Product_pair (Op_cat A) B a (@fapp0 A B F a)) (@Product_pair (Op_cat A) B a b) (@Product_pair (Hom_cat (Op_cat A) a a) (Hom_cat B (@fapp0 A B F a) b) (@id A a) f) (@id B (@fapp0 A B F a))))
   (@eq_ap (Hom B (@fapp0 A B F a) b) (Hom A a (@fapp0 B A G b)) (λ v : τ (Hom B (@fapp0 A B F a) b), (@fapp0 (Hom_cat B (@fapp0 A B F a) b) (Hom_cat A a (@fapp0 B A G b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) v))
     (@Hom_fapp0 B (@fapp0 A B F a) (@fapp0 A B F a) (@fapp0 A B F a) b (@id B (@fapp0 A B F a)) f (@id B (@fapp0 A B F a))) f (@hom_comparison_source_id_path B (@fapp0 A B F a) b f));

// Inverse mate formula from the same selected inverse’s native naturality.
protected symbol hom_comparison_mate_from_formula [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) (b : τ (Obj B))
 (g : τ (Hom A a (@fapp0 B A G b)))
 : τ (@= (Hom B (@fapp0 A B F a) b) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G b)) b (@fapp0 (Hom_cat A (@fapp0 B A G b) (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G b)) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G b) b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G b))) (@fapp1_fapp0 A B F a (@fapp0 B A G b) g)) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) g))
≔ @eq_trans (Hom B (@fapp0 A B F a) b) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G b)) b (@fapp0 (Hom_cat A (@fapp0 B A G b) (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G b)) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G b) b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G b))) (@fapp1_fapp0 A B F a (@fapp0 B A G b) g)) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@Hom_fapp0 A (@fapp0 B A G b) a (@fapp0 B A G b) (@fapp0 B A G b) g (@id A (@fapp0 B A G b)) (@id A (@fapp0 B A G b)))) (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) g)
   (@hom_to_path (Hom_cat B (@fapp0 A B F a) b) (B1 (@fapp0 A B F a) b) _ _ (@fdapp1_int_cell (Product_cat (Op_cat A) B) (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i) (@Product_pair (Op_cat A) B (@fapp0 B A G b) b) (@Product_pair (Op_cat A) B a b) (@Product_pair (Hom_cat (Op_cat A) (@fapp0 B A G b) a) (Hom_cat B b b) g (@id B b)) (@id A (@fapp0 B A G b))))
   (@eq_ap (Hom A a (@fapp0 B A G b)) (Hom B (@fapp0 A B F a) b) (λ v : τ (Hom A a (@fapp0 B A G b)), (@fapp0 (Hom_cat A a (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F a) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) v))
     (@Hom_fapp0 A (@fapp0 B A G b) a (@fapp0 B A G b) (@fapp0 B A G b) g (@id A (@fapp0 B A G b)) (@id A (@fapp0 B A G b))) g (@hom_comparison_target_id_path A a (@fapp0 B A G b) g));

// The original forward comparison applied to id_Fa.
protected symbol hom_comparison_unit_value [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A)) : τ (Hom A a (@fapp0 B A G (@fapp0 A B F a)))
≔ @fapp0 (Hom_cat B (@fapp0 A B F a) (@fapp0 A B F a)) (Hom_cat A a (@fapp0 B A G (@fapp0 A B F a))) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B a (@fapp0 A B F a)) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id B (@fapp0 A B F a));

// The original selected inverse applied to id_Gb.
protected symbol hom_comparison_counit_value [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (b : τ (Obj B)) : τ (Hom B (@fapp0 A B F (@fapp0 B A G b)) b)
≔ @fapp0 (Hom_cat A (@fapp0 B A G b) (@fapp0 B A G b)) (Hom_cat B (@fapp0 A B F (@fapp0 B A G b)) b) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B (@fapp0 B A G b) b) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@id A (@fapp0 B A G b));

// The left mate formula and original inverse cut yield the calculated triangle.
protected symbol hom_comparison_calculated_triangle_left [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A))
 : τ (@= (Hom B (@fapp0 A B F a) (@fapp0 A B F a)) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))) (@fapp0 A B F a) (@hom_comparison_counit_value A B A1 B1 F G i (@fapp0 A B F a)) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@hom_comparison_unit_value A B A1 B1 F G i a))) (@id B (@fapp0 A B F a)))
≔ @eq_trans (Hom B (@fapp0 A B F a) (@fapp0 A B F a)) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))) (@fapp0 A B F a) (@hom_comparison_counit_value A B A1 B1 F G i (@fapp0 A B F a)) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@hom_comparison_unit_value A B A1 B1 F G i a))) (@fapp0 (Hom_cat A a (@fapp0 B A G (@fapp0 A B F a))) (Hom_cat B (@fapp0 A B F a) (@fapp0 A B F a)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B)) (@Product_pair (Op_cat A) B a (@fapp0 A B F a)) (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@hom_comparison_unit_value A B A1 B1 F G i a)) (@id B (@fapp0 A B F a))
   (@hom_comparison_mate_from_formula A B A1 B1 F G i a (@fapp0 A B F a) (@hom_comparison_unit_value A B A1 B1 F G i a))
   (@hom_comparison_prof_component_left A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i a (@fapp0 A B F a) (@id B (@fapp0 A B F a)));

// The right mate formula and original inverse cut yield the calculated triangle.
protected symbol hom_comparison_calculated_triangle_right [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (b : τ (Obj B))
 : τ (@= (Hom A (@fapp0 B A G b) (@fapp0 B A G b)) (@comp_fapp0 A (@fapp0 B A G b) (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@hom_comparison_counit_value A B A1 B1 F G i b)) (@hom_comparison_unit_value A B A1 B1 F G i (@fapp0 B A G b))) (@id A (@fapp0 B A G b)))
≔ @eq_trans (Hom A (@fapp0 B A G b) (@fapp0 B A G b)) (@comp_fapp0 A (@fapp0 B A G b) (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@hom_comparison_counit_value A B A1 B1 F G i b)) (@hom_comparison_unit_value A B A1 B1 F G i (@fapp0 B A G b))) (@fapp0 (Hom_cat B (@fapp0 A B F (@fapp0 B A G b)) b) (Hom_cat A (@fapp0 B A G b) (@fapp0 B A G b)) (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) (@Product_pair (Op_cat A) B (@fapp0 B A G b) b) (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i)) (@hom_comparison_counit_value A B A1 B1 F G i b)) (@id A (@fapp0 B A G b))
   (@hom_comparison_mate_to_formula A B A1 B1 F G i (@fapp0 B A G b) b (@hom_comparison_counit_value A B A1 B1 F G i b))
   (@hom_comparison_prof_component_right A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G) i (@fapp0 B A G b) b (@id A (@fapp0 B A G b)));

// Ordinary congruence of composition on two already constructed arrows.
protected symbol hom_comparison_comp_path [C : Cat] (x y z : τ (Obj C))
 (g g0 : τ (Hom C y z)) (f f0 : τ (Hom C x y))
 (pg : τ (@= (Hom C y z) g g0)) (pf : τ (@= (Hom C x y) f f0))
 : τ (@= (Hom C x z) (@comp_fapp0 C x y z g f) (@comp_fapp0 C x y z g0 f0))
≔ @eq_trans (Hom C x z) (@comp_fapp0 C x y z g f)
   (@comp_fapp0 C x y z g f0) (@comp_fapp0 C x y z g0 f0)
   (@eq_ap (Hom C x y) (Hom C x z) (λ h : τ (Hom C x y), @comp_fapp0 C x y z g h) f f0 pf)
   (@eq_ap (Hom C y z) (Hom C x z) (λ h : τ (Hom C y z), @comp_fapp0 C x y z h f0) g g0 pg);

// Replace the calculated values by the actual whole η/ε components.
protected symbol hom_comparison_actual_triangle_left [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (a : τ (Obj A))
 : τ (@= (Hom B (@fapp0 A B F a) (@fapp0 A B F a)) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))) (@fapp0 A B F a) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) (@fapp0 A B F a) (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) a (@one_cat_hom_comparison_unit A B A1 B1 F G i)))) (@id B (@fapp0 A B F a)))
≔ @eq_trans (Hom B (@fapp0 A B F a) (@fapp0 A B F a)) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))) (@fapp0 A B F a) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) (@fapp0 A B F a) (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) a (@one_cat_hom_comparison_unit A B A1 B1 F G i)))) (@comp_fapp0 B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))) (@fapp0 A B F a) (@hom_comparison_counit_value A B A1 B1 F G i (@fapp0 A B F a)) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@hom_comparison_unit_value A B A1 B1 F G i a))) (@id B (@fapp0 A B F a))
   (@hom_comparison_comp_path B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))) (@fapp0 A B F a) (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) (@fapp0 A B F a) (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@hom_comparison_counit_value A B A1 B1 F G i (@fapp0 A B F a)) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) a (@one_cat_hom_comparison_unit A B A1 B1 F G i))) (@fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) (@hom_comparison_unit_value A B A1 B1 F G i a))
     (@one_cat_hom_comparison_counit_component_path A B A1 B1 F G i (@fapp0 A B F a))
     (@eq_ap (Hom A a (@fapp0 B A G (@fapp0 A B F a))) (Hom B (@fapp0 A B F a) (@fapp0 A B F (@fapp0 B A G (@fapp0 A B F a))))
       (λ h : τ (Hom A a (@fapp0 B A G (@fapp0 A B F a))), @fapp1_fapp0 A B F a (@fapp0 B A G (@fapp0 A B F a)) h)
       (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) a (@one_cat_hom_comparison_unit A B A1 B1 F G i)) (@hom_comparison_unit_value A B A1 B1 F G i a) (@one_cat_hom_comparison_unit_component_path A B A1 B1 F G i a)))
   (@hom_comparison_calculated_triangle_left A B A1 B1 F G i a);

// The right triangle at the actual whole η/ε components.
protected symbol hom_comparison_actual_triangle_right [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) (b : τ (Obj B))
 : τ (@= (Hom A (@fapp0 B A G b) (@fapp0 B A G b)) (@comp_fapp0 A (@fapp0 B A G b) (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) b (@one_cat_hom_comparison_counit A B A1 B1 F G i))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) (@fapp0 B A G b) (@one_cat_hom_comparison_unit A B A1 B1 F G i))) (@id A (@fapp0 B A G b)))
≔ @eq_trans (Hom A (@fapp0 B A G b) (@fapp0 B A G b)) (@comp_fapp0 A (@fapp0 B A G b) (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) b (@one_cat_hom_comparison_counit A B A1 B1 F G i))) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) (@fapp0 B A G b) (@one_cat_hom_comparison_unit A B A1 B1 F G i))) (@comp_fapp0 A (@fapp0 B A G b) (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@hom_comparison_counit_value A B A1 B1 F G i b)) (@hom_comparison_unit_value A B A1 B1 F G i (@fapp0 B A G b))) (@id A (@fapp0 B A G b))
   (@hom_comparison_comp_path A (@fapp0 B A G b) (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) b (@one_cat_hom_comparison_counit A B A1 B1 F G i))) (@fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b (@hom_comparison_counit_value A B A1 B1 F G i b)) (@tapp0_fapp0 A A (@id_func A) (@comp_cat_fapp0 A B A G F) (@fapp0 B A G b) (@one_cat_hom_comparison_unit A B A1 B1 F G i)) (@hom_comparison_unit_value A B A1 B1 F G i (@fapp0 B A G b))
     (@eq_ap (Hom B (@fapp0 A B F (@fapp0 B A G b)) b) (Hom A (@fapp0 B A G (@fapp0 A B F (@fapp0 B A G b))) (@fapp0 B A G b))
       (λ h : τ (Hom B (@fapp0 A B F (@fapp0 B A G b)) b), @fapp1_fapp0 B A G (@fapp0 A B F (@fapp0 B A G b)) b h)
       (@tapp0_fapp0 B B (@comp_cat_fapp0 B A B F G) (@id_func B) b (@one_cat_hom_comparison_counit A B A1 B1 F G i)) (@hom_comparison_counit_value A B A1 B1 F G i b) (@one_cat_hom_comparison_counit_component_path A B A1 B1 F G i b))
     (@one_cat_hom_comparison_unit_component_path A B A1 B1 F G i (@fapp0 B A G b)))
   (@hom_comparison_calculated_triangle_right A B A1 B1 F G i b);

// Left triangle (ε⋅F)∘(F⋅η): transf of the actual whole constructions.
symbol one_cat_hom_comparison_triangle_left_transf [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) : τ (@Transf A B F F)
≔ (@comp_fapp0 (Functor_cat A B) F (@comp_cat_fapp0 A B B (@comp_cat_fapp0 B A B F G) F) F
  (@transf_prewhisker A B B F (@comp_cat_fapp0 B A B F G) (@id_func B) (@one_cat_hom_comparison_counit A B A1 B1 F G i))
  (@transf_postwhisker A A B F (@id_func A) (@comp_cat_fapp0 A B A G F) (@one_cat_hom_comparison_unit A B A1 B1 F G i)));

// Left triangle (ε⋅F)∘(F⋅η): modification of the actual whole constructions.
symbol one_cat_hom_comparison_triangle_left_modification [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (Hom (@Transf_cat A B F F) (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i) (@id (Functor_cat A B) F))
≔ @one_cat_modification A B B1 F F (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i) (@id (Functor_cat A B) F)
   (λ a : τ (Obj A), @path_to_hom (Hom_cat B (@fapp0 A B F a) (@fapp0 A B F a))
      (@tapp0_fapp0 A B F F a (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i)) (@id B (@fapp0 A B F a))
      (@hom_comparison_actual_triangle_left A B A1 B1 F G i a));

// Left triangle (ε⋅F)∘(F⋅η): path of the actual whole constructions.
symbol one_cat_hom_comparison_triangle_left_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@= (@Transf A B F F) (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i) (@id (Functor_cat A B) F))
≔ @hom_to_path (@Transf_cat A B F F)
   ((@one_cat_functor_category A B B1) F F) (@one_cat_hom_comparison_triangle_left_transf A B A1 B1 F G i) (@id (Functor_cat A B) F)
   (@one_cat_hom_comparison_triangle_left_modification A B A1 B1 F G i);

// Right triangle (G⋅ε)∘(η⋅G): transf of the actual whole constructions.
symbol one_cat_hom_comparison_triangle_right_transf [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G))) : τ (@Transf B A G G)
≔ (@comp_fapp0 (Functor_cat B A) G (@comp_cat_fapp0 B A A (@comp_cat_fapp0 A B A G F) G) G
  (@transf_postwhisker B B A G (@comp_cat_fapp0 B A B F G) (@id_func B) (@one_cat_hom_comparison_counit A B A1 B1 F G i))
  (@transf_prewhisker B A A G (@id_func A) (@comp_cat_fapp0 A B A G F) (@one_cat_hom_comparison_unit A B A1 B1 F G i)));

// Right triangle (G⋅ε)∘(η⋅G): modification of the actual whole constructions.
symbol one_cat_hom_comparison_triangle_right_modification [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (Hom (@Transf_cat B A G G) (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i) (@id (Functor_cat B A) G))
≔ @one_cat_modification B A A1 G G (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i) (@id (Functor_cat B A) G)
   (λ b : τ (Obj B), @path_to_hom (Hom_cat A (@fapp0 B A G b) (@fapp0 B A G b))
      (@tapp0_fapp0 B A G G b (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i)) (@id A (@fapp0 B A G b))
      (@hom_comparison_actual_triangle_right A B A1 B1 F G i b));

// Right triangle (G⋅ε)∘(η⋅G): path of the actual whole constructions.
symbol one_cat_hom_comparison_triangle_right_path [A B : Cat] (A1 : τ (IsNCat (cat_succ cat_zero) A))
 (B1 : τ (IsNCat (cat_succ cat_zero) B)) (F : τ (Functor A B)) (G : τ (Functor B A))
 (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)))
 : τ (@= (@Transf B A G G) (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i) (@id (Functor_cat B A) G))
≔ @hom_to_path (@Transf_cat B A G G)
   ((@one_cat_functor_category B A A1) G G) (@one_cat_hom_comparison_triangle_right_transf A B A1 B1 F G i) (@id (Functor_cat B A) G)
   (@one_cat_hom_comparison_triangle_right_modification A B A1 B1 F G i);
