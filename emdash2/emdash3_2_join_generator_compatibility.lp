/*
  Whole walking-generator compatibility for directed join maps.

  Two propositional computation boundaries connect the active generic owners:
  the component of a reindexed profunctor map agrees with the original whole
  component at the mapped endpoint pair, and the whole cross observed through
  a WalkingArrow map agrees with that map's ordinary hom action.  Composing
  those boundaries with the existing join-extension cross beta derives the
  whole generator beta of join_map_func.

  All comparisons remain whole Terminal-indexed functors. Equality-induced
  transformations retain their hom action; point equations are projections.
  No runtime rule, proof-time unifier, selected simplex filler, broad join eta,
  or Cat-valued mapping-data total is added.
*/

require open emdash.emdash3_2_join_cross_compatibility;

// The terminal-indexed whole cross obtained from the profunctor observation.
symbol join_map_observe_walking_generator_func
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (Functor
      Terminal_cat
      (Hom_cat C
        (@fapp0 WalkingArrow_cat C H walking_arrow_src)
        (@fapp0 WalkingArrow_cat C H walking_arrow_tgt)))
≔ @Fibre_func
    (Product_cat (Op_cat Terminal_cat) Terminal_cat)
    (@Terminal_prof Terminal_cat Terminal_cat)
    (@Prof_reindex
      C Terminal_cat C Terminal_cat
      (@Unit_prof C)
      (@join_map_observe_left Terminal_cat Terminal_cat C H)
      (@join_map_observe_right Terminal_cat Terminal_cat C H))
    (@join_map_observe_cross Terminal_cat Terminal_cat C H)
    walking_arrow_cross_base;

// The same intended whole action read through the ordinary hom action of H.
symbol walking_generator_fapp1_func
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (Functor
      Terminal_cat
      (Hom_cat C
        (@fapp0 WalkingArrow_cat C H walking_arrow_src)
        (@fapp0 WalkingArrow_cat C H walking_arrow_tgt)))
≔ @comp_cat_fapp0
    Terminal_cat
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    (Hom_cat C
      (@fapp0 WalkingArrow_cat C H walking_arrow_src)
      (@fapp0 WalkingArrow_cat C H walking_arrow_tgt))
    (@fapp1_func
      WalkingArrow_cat C H walking_arrow_src walking_arrow_tgt)
    walking_arrow_generator_func;

// Scoped whole comparison proposed at the observation/action boundary.
constant symbol join_map_observe_walking_generator_path
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (@=
      (Functor Terminal_cat
        (Hom_cat C
          (@fapp0 WalkingArrow_cat C H walking_arrow_src)
          (@fapp0 WalkingArrow_cat C H walking_arrow_tgt)))
      (@join_map_observe_walking_generator_func C H)
      (@walking_generator_fapp1_func C H));

// Evaluating the whole comparison yields the ordinary generating-arrow view.
symbol join_map_observe_walking_generator_at_path
  [C : Cat]
  (H : τ (Functor WalkingArrow_cat C))
  : τ (@=
      (Hom C
        (@fapp0 WalkingArrow_cat C H walking_arrow_src)
        (@fapp0 WalkingArrow_cat C H walking_arrow_tgt))
      (@fapp0
        Terminal_cat
        (Hom_cat C
          (@fapp0 WalkingArrow_cat C H walking_arrow_src)
          (@fapp0 WalkingArrow_cat C H walking_arrow_tgt))
        (@join_map_observe_walking_generator_func C H)
        Terminal_obj)
      (@fapp1_fapp0
        WalkingArrow_cat C H
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_ap
    (Functor Terminal_cat
      (Hom_cat C
        (@fapp0 WalkingArrow_cat C H walking_arrow_src)
        (@fapp0 WalkingArrow_cat C H walking_arrow_tgt)))
    (Hom C
      (@fapp0 WalkingArrow_cat C H walking_arrow_src)
      (@fapp0 WalkingArrow_cat C H walking_arrow_tgt))
    (λ F : τ (Functor Terminal_cat
        (Hom_cat C
          (@fapp0 WalkingArrow_cat C H walking_arrow_src)
          (@fapp0 WalkingArrow_cat C H walking_arrow_tgt))),
      @fapp0
        Terminal_cat
        (Hom_cat C
          (@fapp0 WalkingArrow_cat C H walking_arrow_src)
          (@fapp0 WalkingArrow_cat C H walking_arrow_tgt))
        F Terminal_obj)
    (@join_map_observe_walking_generator_func C H)
    (@walking_generator_fapp1_func C H)
    (@join_map_observe_walking_generator_path C H);
// Mapped base pair of a profunctor reindexing.
symbol prof_reindex_mapped_pair
  [A A' B B' : Cat]
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a : τ (Obj (Op_cat A')))
  (b : τ (Obj B'))
  : τ (Obj (Product_cat (Op_cat A) B))
≔ @Product_pair
    (Op_cat A) B
    (@fapp0 A' A F a)
    (@fapp0 B' B G b);

// Propositional component computation for the whole reindexed vertical map.
constant symbol prof_reindex_transf_component_path
  [A A' B B' : Cat]
  [R S : τ (Prof A B)]
  (r : τ (ProfMap R S))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a : τ (Obj (Op_cat A')))
  (b : τ (Obj B'))
  : τ (@=
      (Obj (Functor_cat
        (Fibre_cat R (@prof_reindex_mapped_pair A A' B B' F G a b))
        (Fibre_cat S (@prof_reindex_mapped_pair A A' B B' F G a b))))
      (@Fibre_func
        (Product_cat (Op_cat A') B')
        (@Prof_reindex A A' B B' R F G)
        (@Prof_reindex A A' B B' S F G)
        (@Prof_reindex_transf A A' B B' R S r F G)
        (@Product_pair (Op_cat A') B' a b))
      (@Fibre_func
        (Product_cat (Op_cat A) B)
        R S r
        (@prof_reindex_mapped_pair A A' B B' F G a b)));

// Equality-induced whole transformation retains the next component action.
symbol prof_reindex_transf_component_cell
  [A A' B B' : Cat]
  [R S : τ (Prof A B)]
  (r : τ (ProfMap R S))
  (F : τ (Functor A' A))
  (G : τ (Functor B' B))
  (a : τ (Obj (Op_cat A')))
  (b : τ (Obj B'))
  : τ (Transf
      (@Fibre_func
        (Product_cat (Op_cat A') B')
        (@Prof_reindex A A' B B' R F G)
        (@Prof_reindex A A' B B' S F G)
        (@Prof_reindex_transf A A' B B' R S r F G)
        (@Product_pair (Op_cat A') B' a b))
      (@Fibre_func
        (Product_cat (Op_cat A) B)
        R S r
        (@prof_reindex_mapped_pair A A' B B' F G a b)))
≔ @path_to_hom
    (Functor_cat
      (Fibre_cat R (@prof_reindex_mapped_pair A A' B B' F G a b))
      (Fibre_cat S (@prof_reindex_mapped_pair A A' B B' F G a b)))
    (@Fibre_func
      (Product_cat (Op_cat A') B')
      (@Prof_reindex A A' B B' R F G)
      (@Prof_reindex A A' B B' S F G)
      (@Prof_reindex_transf A A' B B' R S r F G)
      (@Product_pair (Op_cat A') B' a b))
    (@Fibre_func
      (Product_cat (Op_cat A) B)
      R S r
      (@prof_reindex_mapped_pair A A' B B' F G a b))
    (@prof_reindex_transf_component_path
      A A' B B' R S r F G a b);
// Source cross component selected by F(*) and G(*).
symbol join_map_source_generator_func
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (Functor
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
≔ @Fibre_func
    (Product_cat (Op_cat A2) B2)
    (@Terminal_prof A2 B2)
    (@Prof_reindex
      (@Join_cat A2 B2) A2
      (@Join_cat A2 B2) B2
      (@Unit_prof (@Join_cat A2 B2))
      (@join_fst_func A2 B2)
      (@join_snd_func A2 B2))
    (@join_cross_transf A2 B2)
    (@Product_pair
      (Op_cat A2) B2
      (@fapp0 Terminal_cat A2 F Terminal_obj)
      (@fapp0 Terminal_cat B2 G Terminal_obj));

// Ordinary hom action of the induced map on the whole walking generator.
symbol join_map_target_generator_func
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (Functor
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
≔ @comp_cat_fapp0
    Terminal_cat
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    (Hom_cat
      (@Join_cat A2 B2)
      (@fapp0 A2 (@Join_cat A2 B2)
        (@join_fst_func A2 B2)
        (@fapp0 Terminal_cat A2 F Terminal_obj))
      (@fapp0 B2 (@Join_cat A2 B2)
        (@join_snd_func A2 B2)
        (@fapp0 Terminal_cat B2 G Terminal_obj)))
    (@fapp1_func
      WalkingArrow_cat
      (@Join_cat A2 B2)
      (@join_map_func
        Terminal_cat Terminal_cat A2 B2 F G)
      walking_arrow_src walking_arrow_tgt)
    walking_arrow_generator_func;

// Object data whose extension is the ordinary map between the two joins.
symbol join_map_generator_data
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@JoinMapObjectData
      Terminal_cat Terminal_cat (@Join_cat A2 B2))
≔ @Struct_sigma
    (Functor Terminal_cat (@Join_cat A2 B2))
    (λ first : τ (Functor Terminal_cat (@Join_cat A2 B2)),
      @Σ_
        (Functor Terminal_cat (@Join_cat A2 B2))
        (λ second : τ (Functor Terminal_cat (@Join_cat A2 B2)),
          Obj (@Prof_transf_cat
            (@Join_cat A2 B2)
            Terminal_cat
            (@Join_cat A2 B2)
            Terminal_cat
            (@Terminal_prof Terminal_cat Terminal_cat)
            first
            (@Unit_prof (@Join_cat A2 B2))
            second)))
    (@join_map_left_func Terminal_cat Terminal_cat A2 B2 F)
    (@Struct_sigma
      (Functor Terminal_cat (@Join_cat A2 B2))
      (λ second : τ (Functor Terminal_cat (@Join_cat A2 B2)),
        Obj (@Prof_transf_cat
          (@Join_cat A2 B2)
          Terminal_cat
          (@Join_cat A2 B2)
          Terminal_cat
          (@Terminal_prof Terminal_cat Terminal_cat)
          (@join_map_left_func Terminal_cat Terminal_cat A2 B2 F)
          (@Unit_prof (@Join_cat A2 B2))
          second))
      (@join_map_right_func Terminal_cat Terminal_cat A2 B2 G)
      (@join_map_cross_transf Terminal_cat Terminal_cat A2 B2 F G));

// Whole primitive component of that data at the walking-arrow endpoint pair.
symbol join_map_primitive_generator_func
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (Functor
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
≔ @Fibre_func
    (Product_cat (Op_cat Terminal_cat) Terminal_cat)
    (@Terminal_prof Terminal_cat Terminal_cat)
    (@join_map_target_prof
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_generator_data A2 B2 F G))
    (@join_map_extend_cross
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_generator_data A2 B2 F G))
    walking_arrow_cross_base;

// Evaluate the existing whole join-extension beta at the generator base pair.
symbol join_map_generator_observed_primitive_func_path
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj)))))
      (@join_map_observe_walking_generator_func
        (@Join_cat A2 B2)
        (@join_map_extend_object
          Terminal_cat Terminal_cat (@Join_cat A2 B2)
          (@join_map_generator_data A2 B2 F G)))
      (@join_map_primitive_generator_func A2 B2 F G))
≔ @eq_ap
    (Obj (@JoinCross_cat
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_generator_data A2 B2 F G)))
    (Obj (Functor_cat
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj)))))
    (λ cross : τ (Obj (@JoinCross_cat
        Terminal_cat Terminal_cat (@Join_cat A2 B2)
        (@join_map_generator_data A2 B2 F G))),
      @Fibre_func
        (Product_cat (Op_cat Terminal_cat) Terminal_cat)
        (@Terminal_prof Terminal_cat Terminal_cat)
        (@join_map_target_prof
          Terminal_cat Terminal_cat (@Join_cat A2 B2)
          (@join_map_generator_data A2 B2 F G))
        cross walking_arrow_cross_base)
    (@join_map_observe_cross
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_extend_object
        Terminal_cat Terminal_cat (@Join_cat A2 B2)
        (@join_map_generator_data A2 B2 F G)))
    (@join_map_extend_cross
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_generator_data A2 B2 F G))
    (@join_map_extend_cross_beta
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_generator_data A2 B2 F G));

// The primitive component is the reindexed source cross component.
symbol join_map_generator_primitive_source_func_path
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj)))))
      (@join_map_primitive_generator_func A2 B2 F G)
      (@join_map_source_generator_func A2 B2 F G))
≔ @prof_reindex_transf_component_path
    A2 Terminal_cat B2 Terminal_cat
    (@Terminal_prof A2 B2)
    (@Prof_reindex
      (@Join_cat A2 B2) A2
      (@Join_cat A2 B2) B2
      (@Unit_prof (@Join_cat A2 B2))
      (@join_fst_func A2 B2)
      (@join_snd_func A2 B2))
    (@join_cross_transf A2 B2)
    F G Terminal_obj Terminal_obj;

// Rigid target of the observation/action comparison before folding the
// extension back to the readable join_map_func owner.
symbol join_map_extension_target_generator_func
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (Functor
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
≔ @walking_generator_fapp1_func
    (@Join_cat A2 B2)
    (@join_map_extend_object
      Terminal_cat Terminal_cat (@Join_cat A2 B2)
      (@join_map_generator_data A2 B2 F G));

symbol join_map_extension_target_generator_path
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Obj (Functor_cat
        Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj)))))
      (@join_map_extension_target_generator_func A2 B2 F G)
      (@join_map_target_generator_func A2 B2 F G))
≔ @eq_refl
    (Obj (Functor_cat
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj)))))
    (@join_map_extension_target_generator_func A2 B2 F G);

// Rigid two-step route from the primitive supplied cross to the extension's
// ordinary generator action.
symbol join_map_generator_primitive_extension_path
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Functor Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj))))
      (@join_map_primitive_generator_func A2 B2 F G)
      (@join_map_extension_target_generator_func A2 B2 F G))
≔ @eq_trans
    (Functor Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
    (@join_map_primitive_generator_func A2 B2 F G)
    (@join_map_observe_walking_generator_func
      (@Join_cat A2 B2)
      (@join_map_extend_object
        Terminal_cat Terminal_cat (@Join_cat A2 B2)
        (@join_map_generator_data A2 B2 F G)))
    (@join_map_extension_target_generator_func A2 B2 F G)
    (@eq_sym _ _ _
      (@join_map_generator_observed_primitive_func_path A2 B2 F G))
    (@join_map_observe_walking_generator_path
      (@Join_cat A2 B2)
      (@join_map_extend_object
        Terminal_cat Terminal_cat (@Join_cat A2 B2)
        (@join_map_generator_data A2 B2 F G)));

symbol join_map_generator_primitive_target_path
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Functor Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj))))
      (@join_map_primitive_generator_func A2 B2 F G)
      (@join_map_target_generator_func A2 B2 F G))
≔ @eq_trans
    (Functor Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
    (@join_map_primitive_generator_func A2 B2 F G)
    (@join_map_extension_target_generator_func A2 B2 F G)
    (@join_map_target_generator_func A2 B2 F G)
    (@join_map_generator_primitive_extension_path A2 B2 F G)
    (@join_map_extension_target_generator_path A2 B2 F G);

// Derived propositional higher-constructor computation at the whole generator
// owner. No independent generator beta is postulated.
symbol join_map_generator_beta
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Functor Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj))))
      (@join_map_source_generator_func A2 B2 F G)
      (@join_map_target_generator_func A2 B2 F G))
≔ @eq_trans
    (Functor
      Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
    (@join_map_source_generator_func A2 B2 F G)
    (@join_map_primitive_generator_func A2 B2 F G)
    (@join_map_target_generator_func A2 B2 F G)
    (@eq_sym _ _ _
      (@join_map_generator_primitive_source_func_path A2 B2 F G))
    (@join_map_generator_primitive_target_path A2 B2 F G);

// Point projection retains its whole-functor origin.
symbol join_map_generator_at_beta
  [A2 B2 : Cat]
  (F : τ (Functor Terminal_cat A2))
  (G : τ (Functor Terminal_cat B2))
  : τ (@=
      (Hom
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj)))
      (@fapp0
        Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj)))
        (@join_map_source_generator_func A2 B2 F G)
        Terminal_obj)
      (@fapp1_fapp0
        WalkingArrow_cat
        (@Join_cat A2 B2)
        (@join_map_func Terminal_cat Terminal_cat A2 B2 F G)
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_ap
    (Functor Terminal_cat
      (Hom_cat
        (@Join_cat A2 B2)
        (@fapp0 A2 (@Join_cat A2 B2)
          (@join_fst_func A2 B2)
          (@fapp0 Terminal_cat A2 F Terminal_obj))
        (@fapp0 B2 (@Join_cat A2 B2)
          (@join_snd_func A2 B2)
          (@fapp0 Terminal_cat B2 G Terminal_obj))))
    (Hom
      (@Join_cat A2 B2)
      (@fapp0 A2 (@Join_cat A2 B2)
        (@join_fst_func A2 B2)
        (@fapp0 Terminal_cat A2 F Terminal_obj))
      (@fapp0 B2 (@Join_cat A2 B2)
        (@join_snd_func A2 B2)
        (@fapp0 Terminal_cat B2 G Terminal_obj)))
    (λ K : τ (Functor Terminal_cat
        (Hom_cat
          (@Join_cat A2 B2)
          (@fapp0 A2 (@Join_cat A2 B2)
            (@join_fst_func A2 B2)
            (@fapp0 Terminal_cat A2 F Terminal_obj))
          (@fapp0 B2 (@Join_cat A2 B2)
            (@join_snd_func A2 B2)
            (@fapp0 Terminal_cat B2 G Terminal_obj)))),
      @fapp0 Terminal_cat _ K Terminal_obj)
    (@join_map_source_generator_func A2 B2 F G)
    (@join_map_target_generator_func A2 B2 F G)
    (@join_map_generator_beta A2 B2 F G);
