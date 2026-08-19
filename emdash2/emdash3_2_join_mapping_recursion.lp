/*
  First-stage observation and extension for maps out of a directed join.

  A functor H : A star B -> C restricts wholely to both join branches.  Its
  action on the internally natural join cross-cell is derived from the active
  profunctor/reindexing calculus; no pointwise cross-arrow family or external
  naturality equation is introduced.

  JoinMapObjectData is deliberately only the object classifier

    (first, second, cross).

  It is not advertised as the category of join mapping data: morphisms between
  such triples require a mixed-variance coherent square.  Consequently this
  module exposes the existing join extension and its branch/cross computation,
  but adds no broad join eta, no action-derived-cross beta, and no mapping-
  category equivalence.
*/

require open emdash.emdash3_2_simplex_shapes;

// Whole restriction to the left join branch.
symbol join_map_observe_left_func
  [A B C : Cat]
  : τ (Functor
      (@Functor_cat (@Join_cat A B) C)
      (@Functor_cat A C))
≔ @comp_cat_con_func
    A (@Join_cat A B) C
    (@join_fst_func A B);

// Whole restriction to the right join branch.
symbol join_map_observe_right_func
  [A B C : Cat]
  : τ (Functor
      (@Functor_cat (@Join_cat A B) C)
      (@Functor_cat B C))
≔ @comp_cat_con_func
    B (@Join_cat A B) C
    (@join_snd_func A B);

// Readable direct left restriction.
symbol join_map_observe_left
  [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  : τ (Functor A C)
≔ @comp_cat_fapp0
    A (@Join_cat A B) C
    H (@join_fst_func A B);

// Readable direct right restriction.
symbol join_map_observe_right
  [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  : τ (Functor B C)
≔ @comp_cat_fapp0
    B (@Join_cat A B) C
    H (@join_snd_func A B);

// Proof-time comparison between the whole left restriction and its readable
// direct precomposition view. Neither presentation is selected as a new
// runtime normal form.
symbol join_map_observe_left_path
  [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  : τ (@=
      (Obj (@Functor_cat A C))
      (@fapp0
        (@Functor_cat (@Join_cat A B) C)
        (@Functor_cat A C)
        (@join_map_observe_left_func A B C) H)
      (@join_map_observe_left A B C H))
≔ @eq_refl
    (Obj (@Functor_cat A C))
    (@fapp0
      (@Functor_cat (@Join_cat A B) C)
      (@Functor_cat A C)
      (@join_map_observe_left_func A B C) H);

// Proof-time comparison for the right restriction.
symbol join_map_observe_right_path
  [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  : τ (@=
      (Obj (@Functor_cat B C))
      (@fapp0
        (@Functor_cat (@Join_cat A B) C)
        (@Functor_cat B C)
        (@join_map_observe_right_func A B C) H)
      (@join_map_observe_right A B C H))
≔ @eq_refl
    (Obj (@Functor_cat B C))
    (@fapp0
      (@Functor_cat (@Join_cat A B) C)
      (@Functor_cat B C)
      (@join_map_observe_right_func A B C) H);

// The whole cross observation is the image of join_cross_transf under H.
// Endpoint reindexing is retained at Prof_reindex/Prof_reindex_transf.
symbol join_map_observe_cross
  [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  : τ (Obj
      (@Prof_transf_cat
        C A C B
        (@Terminal_prof A B)
        (@join_map_observe_left A B C H)
        (@Unit_prof C)
        (@join_map_observe_right A B C H)))
≔ @comp_fapp0
    (@Prof_cat A B)
    (@Terminal_prof A B)
    (@Prof_reindex
      (@Join_cat A B) A
      (@Join_cat A B) B
      (@Unit_prof (@Join_cat A B))
      (@join_fst_func A B)
      (@join_snd_func A B))
    (@Prof_reindex
      C A C B
      (@Unit_prof C)
      (@join_map_observe_left A B C H)
      (@join_map_observe_right A B C H))
    (@Prof_reindex_transf
      (@Join_cat A B) A
      (@Join_cat A B) B
      (@Unit_prof (@Join_cat A B))
      (@Prof_reindex
        C (@Join_cat A B)
        C (@Join_cat A B)
        (@Unit_prof C) H H)
      (@Prof_func_hom (@Join_cat A B) C H)
      (@join_fst_func A B)
      (@join_snd_func A B))
    (@join_cross_transf A B);

// One shaped component of the internally natural cross observation.
symbol join_map_observe_cross_at
  [A B C I : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  (a : τ (Functor I A))
  (b : τ (Functor I B))
  : τ (@Prof_hom
      I C C
      (@comp_cat_fapp0
        I A C
        (@join_map_observe_left A B C H) a)
      (@Unit_prof C)
      (@comp_cat_fapp0
        I B C
        (@join_map_observe_right A B C H) b))
≔ @Prof_cell_eval
    I A B C C
    (@Unit_prof C)
    (@join_map_observe_left A B C H)
    (@join_map_observe_right A B C H)
    a b
    (@join_map_observe_cross A B C H);

// Object classifier only.  The Cat-valued coherent-square total remains a
// later prerequisite for a whole observation/extension equivalence.
symbol JoinMapObjectData
  (A B C : Cat)
  : Grpd
≔ `Σ_ first : τ (Functor A C),
    `Σ_ second : τ (Functor B C),
      Obj
        (@Prof_transf_cat
          C A C B
          (@Terminal_prof A B)
          first
          (@Unit_prof C)
          second);

symbol join_map_object_left
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Functor A C)
≔ sigma_Fst d;

symbol join_map_object_right
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Functor B C)
≔ sigma_Fst (sigma_Snd d);

symbol join_map_object_cross
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Obj
      (@Prof_transf_cat
        C A C B
        (@Terminal_prof A B)
        (@join_map_object_left A B C d)
        (@Unit_prof C)
        (@join_map_object_right A B C d)))
≔ sigma_Snd (sigma_Snd d);

// Observe the three object-level fields of a map out of a join.
symbol join_map_observe_object
  [A B C : Cat]
  (H : τ (Functor (@Join_cat A B) C))
  : τ (@JoinMapObjectData A B C)
≔ Struct_sigma
    (@join_map_observe_left A B C H)
    (Struct_sigma
      (@join_map_observe_right A B C H)
      (@join_map_observe_cross A B C H));

// Extend object-level join mapping data through the active join recursor.
symbol join_map_extend_object
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Functor (@Join_cat A B) C)
≔ @join_elim_func
    A B C
    (@join_map_object_left A B C d)
    (@join_map_object_right A B C d)
    (@join_map_object_cross A B C d);

// Primitive cross observation of an extension.  This remains distinct from
// the action-derived join_map_observe_cross until a justified compatibility
// owner is available.
symbol join_map_extend_cross
  [A B C : Cat]
  (d : τ (@JoinMapObjectData A B C))
  : τ (Obj
      (@Prof_transf_cat
        C A C B
        (@Terminal_prof A B)
        (@join_map_object_left A B C d)
        (@Unit_prof C)
        (@join_map_object_right A B C d)))
≔ @join_elim_cross_transf
    A B C
    (@join_map_object_left A B C d)
    (@join_map_object_right A B C d)
    (@join_map_object_cross A B C d);
