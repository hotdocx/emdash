/* Reindexed whole profunctor-map components and their adjunction-assembly
   consumer. The identity images below are whole Prof maps; this reviewer
   does not assert extraction into Transf or a new Adjunction constructor. */
require open emdash.emdash3_2_adjunction_mates;

// Whole fibre functor, with arbitrary endpoint functors and an arbitrary base object.
assert [A A' B B' : Cat] [R S : τ (Prof A B)]
  (r : τ (@ProfMap A B R S)) (F : τ (Functor A' A)) (G : τ (Functor B' B))
  (ab : τ (Obj (Product_cat (Op_cat A') B'))) ⊢
  @tapp0_fapp0 (Product_cat (Op_cat A') B') Cat_cat
    (@Prof_reindex A A' B B' R F G) (@Prof_reindex A A' B B' S F G) ab
    (@Prof_reindex_transf A A' B B' R S r F G)
  ≡ @tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat R S
      (@fapp0 (Product_cat (Op_cat A') B') (Product_cat (Op_cat A) B)
        (@Prof_reindex_base_func A A' B B' F G) ab) r;
// Identity endpoint reindexing agrees whichever constructor projection is exposed first.
assert [A B : Cat] [R S : τ (Prof A B)] (r : τ (@ProfMap A B R S))
  (ab : τ (Obj (Product_cat (Op_cat A) B))) ⊢
  @tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat R S ab
    (@Prof_reindex_transf A A B B R S r (@id_func A) (@id_func B))
  ≡ @tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat R S ab r;

// The projection retains a whole functor: its next Hom action is still available.
assert [A A' B B' : Cat] [R S : τ (Prof A B)]
  (r : τ (@ProfMap A B R S)) (F : τ (Functor A' A)) (G : τ (Functor B' B))
  (ab : τ (Obj (Product_cat (Op_cat A') B')))
  (u v : τ (Obj (@fapp0 (Product_cat (Op_cat A) B) Cat_cat R
    (@fapp0 (Product_cat (Op_cat A') B') (Product_cat (Op_cat A) B)
      (@Prof_reindex_base_func A A' B B' F G) ab)))) ⊢
  @fapp1_func _ _
    (@tapp0_fapp0 (Product_cat (Op_cat A') B') Cat_cat
      (@Prof_reindex A A' B B' R F G) (@Prof_reindex A A' B B' S F G) ab
      (@Prof_reindex_transf A A' B B' R S r F G)) u v
  ≡ @fapp1_func _ _
    (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat R S
      (@fapp0 (Product_cat (Op_cat A') B') (Product_cat (Op_cat A) B)
        (@Prof_reindex_base_func A A' B B' F G) ab) r) u v;
/* UA-1 experiment: identity images as whole profunctor maps, not yet a
   claimed extraction into ordinary Transf. All action stays with owners. */


symbol review_unit_identity_image [A B : Cat]
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

symbol review_counit_identity_image [A B : Cat]
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

// Diagnostic annotations are explicit; no production rule is added.
assert [A B : Cat] (F : τ (Functor A B)) (G : τ (Functor B A))
  (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B))
    (@Hom_prof_along A B A (@id_func A) G)))
  (x y : τ (Obj A)) (h : τ (Hom A x y)) ⊢
  @fapp0 (Hom_cat A x y) (Hom_cat A x (@fapp0 B A G (@fapp0 A B F y)))
    (@tapp0_fapp0 (Product_cat (Op_cat A) A) Cat_cat
      (@Unit_prof A) (@Hom_prof_along A A A (@id_func A) (@comp_cat_fapp0 A B A G F))
      (@Product_pair (Op_cat A) A x y) (@review_unit_identity_image A B F G i)) h
  ≡ @fapp0 (Hom_cat B (@fapp0 A B F x) (@fapp0 A B F y))
      (Hom_cat A x (@fapp0 B A G (@fapp0 A B F y)))
      (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat
        (@Hom_prof_along A B B F (@id_func B)) (@Hom_prof_along A B A (@id_func A) G)
        (@Product_pair (Op_cat A) B x (@fapp0 A B F y))
        (@defiso_to (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B))
          (@Hom_prof_along A B A (@id_func A) G) i)) (@fapp1_fapp0 A B F x y h);
// Dual nonidentity input through the retained inverse.
assert [A B : Cat] (F : τ (Functor A B)) (G : τ (Functor B A))
  (i : τ (@ProfComparison A B (@Hom_prof_along A B B F (@id_func B))
    (@Hom_prof_along A B A (@id_func A) G)))
  (x y : τ (Obj B)) (h : τ (Hom B x y)) ⊢
  @fapp0 (Hom_cat B x y) (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) y)
    (@tapp0_fapp0 (Product_cat (Op_cat B) B) Cat_cat (@Unit_prof B)
      (@Hom_prof_along B B B (@comp_cat_fapp0 B A B F G) (@id_func B))
      (@Product_pair (Op_cat B) B x y) (@review_counit_identity_image A B F G i)) h
  ≡ @fapp0 (Hom_cat A (@fapp0 B A G x) (@fapp0 B A G y))
      (Hom_cat B (@fapp0 A B F (@fapp0 B A G x)) y)
      (@tapp0_fapp0 (Product_cat (Op_cat A) B) Cat_cat
        (@Hom_prof_along A B A (@id_func A) G) (@Hom_prof_along A B B F (@id_func B))
        (@Product_pair (Op_cat A) B (@fapp0 B A G x) y)
        (@defiso_from (Prof_cat A B) (@Hom_prof_along A B B F (@id_func B))
          (@Hom_prof_along A B A (@id_func A) G) i)) (@fapp1_fapp0 B A G x y h);

// Reindexing does not identify unrelated map data.
assertnot [A A' B B' : Cat] [R S : τ (Prof A B)]
  (r s : τ (@ProfMap A B R S)) (F : τ (Functor A' A)) (G : τ (Functor B' B))
  (ab : τ (Obj (Product_cat (Op_cat A') B'))) ⊢
  @tapp0_fapp0 (Product_cat (Op_cat A') B') Cat_cat
    (@Prof_reindex A A' B B' R F G) (@Prof_reindex A A' B B' S F G) ab
    (@Prof_reindex_transf A A' B B' R S r F G)
  ≡ @tapp0_fapp0 (Product_cat (Op_cat A') B') Cat_cat
    (@Prof_reindex A A' B B' R F G) (@Prof_reindex A A' B B' S F G) ab
    (@Prof_reindex_transf A A' B B' R S s F G);
