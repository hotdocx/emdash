/*
  Concrete directed-to-groupoidal comparison from WalkingArrow to Interval.

  The active directed source remains the join-derived WalkingArrow_cat.  A
  whole profunctor cell naturalizes interval_seg across the two terminal join
  endpoints, and join_elim_func gives the structural presentation of the
  comparison.  The deployed unit keeps a stable functor head so its endpoint
  computations are judgmental and its generic hom action remains iterable.
  A whole path records agreement with the join presentation.

  As for ordinary Circle recursion, first-arrow computation is propositional:
  the selected generator is compared with interval_seg by one scoped path.
  No generic Groupoidify reflector, source action, or adjunction is declared.
*/

require open emdash.emdash3_2_groupoidal_interval_hit;
require open emdash.emdash3_2_walking_arrow;

// The two terminal endpoint diagrams in Path(Interval).
symbol walking_interval_left_func
  : τ (Functor Terminal_cat (Path_cat Interval_grpd))
≔ @Const_func Terminal_cat (Path_cat Interval_grpd) interval_i0;

symbol walking_interval_right_func
  : τ (Functor Terminal_cat (Path_cat Interval_grpd))
≔ @Const_func Terminal_cat (Path_cat Interval_grpd) interval_i1;

/*
  Whole natural equipment cell carrying interval_seg between the endpoint
  diagrams.  Its fibre over the unique endpoint pair computes to the constant
  functor selecting interval_seg.
*/
constant symbol walking_interval_seg_cross
  : τ (Obj
      (@Prof_transf_cat
        (Path_cat Interval_grpd)
        Terminal_cat
        (Path_cat Interval_grpd)
        Terminal_cat
        (@Terminal_prof Terminal_cat Terminal_cat)
        walking_interval_left_func
        (@Unit_prof (Path_cat Interval_grpd))
        walking_interval_right_func));

// The cross owner uniquely reconstructs its base, families, and component.
rule @tapp0_fapp0
      _ Cat_cat _ _ _
      walking_interval_seg_cross
  ↪ @Const_func
      Terminal_cat
      (Hom_cat (Path_cat Interval_grpd) interval_i0 interval_i1)
      interval_seg;

// Readable whole fibre owner for the selected path constructor.
symbol walking_interval_seg_cross_func
  : τ (Functor
      Terminal_cat
      (Hom_cat (Path_cat Interval_grpd) interval_i0 interval_i1))
≔ @Fibre_func
    (Product_cat (Op_cat Terminal_cat) Terminal_cat)
    (@Terminal_prof Terminal_cat Terminal_cat)
    (@Prof_reindex
      (Path_cat Interval_grpd) Terminal_cat
      (Path_cat Interval_grpd) Terminal_cat
      (@Unit_prof (Path_cat Interval_grpd))
      walking_interval_left_func walking_interval_right_func)
    walking_interval_seg_cross
    walking_arrow_cross_base;

// Structural join-eliminator presentation of the comparison.
symbol walking_arrow_to_interval_join_func
  : τ (Functor WalkingArrow_cat (Path_cat Interval_grpd))
≔ @join_elim_func
    Terminal_cat Terminal_cat (Path_cat Interval_grpd)
    walking_interval_left_func
    walking_interval_right_func
    walking_interval_seg_cross;

/*
  Stable deployed comparison unit.  The direct head avoids relying on a
  missing generic first-arrow beta for join_elim_func, while the whole path
  below retains the join-derived provenance.
*/
injective symbol walking_arrow_to_interval_func
  : τ (Functor WalkingArrow_cat (Path_cat Interval_grpd));

// Judgmental endpoint computation. The expanded join endpoints are the
// runtime owners; walking_arrow_src/tgt are readable definitions over them.
rule @fapp0 _ _ walking_arrow_to_interval_func
      (@fapp0
        Terminal_cat
        (@Join_cat Terminal_cat Terminal_cat)
        (@join_fst_func Terminal_cat Terminal_cat)
        Terminal_obj)
  ↪ interval_i0
with @fapp0 _ _ walking_arrow_to_interval_func
      (@fapp0
        Terminal_cat
        (@Join_cat Terminal_cat Terminal_cat)
        (@join_snd_func Terminal_cat Terminal_cat)
        Terminal_obj)
  ↪ interval_i1;

// Whole agreement with the join-eliminator presentation.
constant symbol walking_arrow_to_interval_join_path
  : τ (@=
      (Functor WalkingArrow_cat (Path_cat Interval_grpd))
      walking_arrow_to_interval_func
      walking_arrow_to_interval_join_func);

// Typed views of judgmental endpoint computation.
symbol walking_arrow_to_interval_beta_i0
  : τ (@= Interval_grpd
      (@fapp0
        WalkingArrow_cat (Path_cat Interval_grpd)
        walking_arrow_to_interval_func walking_arrow_src)
      interval_i0)
≔ @eq_refl Interval_grpd interval_i0;

symbol walking_arrow_to_interval_beta_i1
  : τ (@= Interval_grpd
      (@fapp0
        WalkingArrow_cat (Path_cat Interval_grpd)
        walking_arrow_to_interval_func walking_arrow_tgt)
      interval_i1)
≔ @eq_refl Interval_grpd interval_i1;

/*
  Selected first-arrow comparison.  It is scoped propositional signature data
  rather than a competing fapp1 runtime rule; the whole hom action below stays
  generic and iterable.
*/
constant symbol walking_arrow_to_interval_beta_generator
  : τ (@=
      (@= Interval_grpd interval_i0 interval_i1)
      (@fapp1_fapp0
        WalkingArrow_cat
        (Path_cat Interval_grpd)
        walking_arrow_to_interval_func
        walking_arrow_src walking_arrow_tgt
        walking_arrow_generator)
      interval_seg);

// Whole hom action of the comparison between the selected endpoints.
symbol walking_arrow_to_interval_hom_func
  : τ (Functor
      (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      (Hom_cat
        (Path_cat Interval_grpd)
        interval_i0 interval_i1))
≔ @fapp1_func
    WalkingArrow_cat
    (Path_cat Interval_grpd)
    walking_arrow_to_interval_func
    walking_arrow_src walking_arrow_tgt;

// One retained next action of the deployed comparison unit.
symbol walking_arrow_to_interval_next_func
  : τ (Functor
      (Hom_cat
        (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
        walking_arrow_generator walking_arrow_generator)
      (Hom_cat
        (Hom_cat
          (Path_cat Interval_grpd)
          interval_i0 interval_i1)
        (@fapp1_fapp0
          WalkingArrow_cat
          (Path_cat Interval_grpd)
          walking_arrow_to_interval_func
          walking_arrow_src walking_arrow_tgt
          walking_arrow_generator)
        (@fapp1_fapp0
          WalkingArrow_cat
          (Path_cat Interval_grpd)
          walking_arrow_to_interval_func
          walking_arrow_src walking_arrow_tgt
          walking_arrow_generator)))
≔ @fapp1_func
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    (Hom_cat (Path_cat Interval_grpd) interval_i0 interval_i1)
    walking_arrow_to_interval_hom_func
    walking_arrow_generator walking_arrow_generator;
