/*
  Whole primitive/action-derived join-cross compatibility.

  Applying a join extension to the source join-cross cell and reading the
  primitive cross datum supplied to the recursor are two whole objects of the
  same profunctor-transformation category. Their equality is the propositional
  higher-constructor computation principle for join elimination. It remains a
  path rather than a runtime rule because the public observed-cross surface is
  a transparent definition and changing it to a stable head would be a wider
  normal-form migration.

  The equality-induced arrow is a whole displayed transformation. Ordinary
  endpoint components, arbitrary shaped components, and base-arrow action are
  derived from it through existing projection owners. No Cat-valued coherent-
  square total, filler constant, rewrite, or proof-time unifier is added.
*/

require open emdash.emdash3_2_join_mapping_recursion;

// Common target family for the two cross objects.
symbol join_map_target_prof
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Catd (Product_cat (Op_cat A) B))
≔ @Prof_reindex
    C A C B
    (@Unit_prof C)
    (@join_map_object_left A B C d)
    (@join_map_object_right A B C d);

// Whole category containing primitive and action-derived cross cells.
symbol JoinCross_cat
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : Cat
≔ @Prof_transf_cat
    C A C B
    (@Terminal_prof A B)
    (@join_map_object_left A B C d)
    (@Unit_prof C)
    (@join_map_object_right A B C d);

// Whole equality type for the missing higher-constructor computation.
symbol JoinCrossCompatibility
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : Grpd
≔ @=
    (Obj (@JoinCross_cat A B C d))
    (@join_map_observe_cross
      A B C
      (@join_map_extend_object A B C d))
    (@join_map_extend_cross A B C d);

// Propositional whole cross beta for join elimination.
constant symbol join_map_extend_cross_beta
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (@JoinCrossCompatibility A B C d);

// Equality-induced whole directed cell between the two cross transfors.
symbol join_map_extend_cross_cell
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Hom
      (@JoinCross_cat A B C d)
      (@join_map_observe_cross
        A B C
        (@join_map_extend_object A B C d))
      (@join_map_extend_cross A B C d))
≔ @path_to_hom
    (@JoinCross_cat A B C d)
    (@join_map_observe_cross
      A B C
      (@join_map_extend_object A B C d))
    (@join_map_extend_cross A B C d)
    (@join_map_extend_cross_beta A B C d);

// Component of the whole compatibility at an endpoint pair.
symbol join_map_extend_cross_component
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  (a : τ (Obj A))
  (b : τ (Obj B))
  : τ (Transf
      (@Fibre_func
        (Product_cat (Op_cat A) B)
        (@Terminal_prof A B)
        (@join_map_target_prof A B C d)
        (@join_map_observe_cross
          A B C
          (@join_map_extend_object A B C d))
        (@Product_pair (Op_cat A) B a b))
      (@Fibre_func
        (Product_cat (Op_cat A) B)
        (@Terminal_prof A B)
        (@join_map_target_prof A B C d)
        (@join_map_extend_cross A B C d)
        (@Product_pair (Op_cat A) B a b)))
≔ @tdapp0_fapp0
    (Product_cat (Op_cat A) B)
    (@Terminal_prof A B)
    (@join_map_target_prof A B C d)
    (@join_map_observe_cross
      A B C
      (@join_map_extend_object A B C d))
    (@join_map_extend_cross A B C d)
    (@Product_pair (Op_cat A) B a b)
    (@join_map_extend_cross_cell A B C d);

// Arbitrary shaped equality obtained by applying the whole path.
symbol join_map_extend_cross_shaped_beta
  [A B C I : Cat]
  (d : τ (@JoinMapObjectData A B C))
  (a : τ (Functor I A))
  (b : τ (Functor I B))
  : τ (@=
      (@Prof_hom
        I C C
        (@comp_cat_fapp0
          I A C (@join_map_object_left A B C d) a)
        (@Unit_prof C)
        (@comp_cat_fapp0
          I B C (@join_map_object_right A B C d) b))
      (@Prof_cell_eval
        I A B C C
        (@Unit_prof C)
        (@join_map_object_left A B C d)
        (@join_map_object_right A B C d)
        a b
        (@join_map_observe_cross
          A B C
          (@join_map_extend_object A B C d)))
      (@Prof_cell_eval
        I A B C C
        (@Unit_prof C)
        (@join_map_object_left A B C d)
        (@join_map_object_right A B C d)
        a b
        (@join_map_extend_cross A B C d)))
≔ @eq_ap
    (Obj (@JoinCross_cat A B C d))
    (@Prof_hom
      I C C
      (@comp_cat_fapp0
        I A C (@join_map_object_left A B C d) a)
      (@Unit_prof C)
      (@comp_cat_fapp0
        I B C (@join_map_object_right A B C d) b))
    (λ cross : τ (Obj (@JoinCross_cat A B C d)),
      @Prof_cell_eval
        I A B C C
        (@Unit_prof C)
        (@join_map_object_left A B C d)
        (@join_map_object_right A B C d)
        a b cross)
    (@join_map_observe_cross
      A B C
      (@join_map_extend_object A B C d))
    (@join_map_extend_cross A B C d)
    (@join_map_extend_cross_beta A B C d);

// Base-arrow action remains the canonical `tdapp1_int_cell` projection of
// `join_map_extend_cross_cell`; no duplicate expanded return-type facade is
// introduced here.
