/*
  Emdash v3.2: curated walking-arrow interface over the directed join.

  No new interval category or generating arrow is postulated here.  The
  walking arrow is Join_cat(1,1); its endpoints are the two join inclusions,
  and its generator is the terminal fibre component of the already internally
  natural join_cross_transf.  Keeping the whole fibre functor retains the
  generator's next hom action for later Gray-square consumers.
*/

require open emdash.emdash3_2;

// The directed interval I is the join of two terminal categories.
symbol WalkingArrow_cat
  : Cat
≔ @Join_cat Terminal_cat Terminal_cat;

// Left endpoint 0 : Obj(I).
symbol walking_arrow_src
  : τ (Obj WalkingArrow_cat)
≔ @fapp0
    Terminal_cat
    WalkingArrow_cat
    (@join_fst_func Terminal_cat Terminal_cat)
    Terminal_obj;

// Right endpoint 1 : Obj(I).
symbol walking_arrow_tgt
  : τ (Obj WalkingArrow_cat)
≔ @fapp0
    Terminal_cat
    WalkingArrow_cat
    (@join_snd_func Terminal_cat Terminal_cat)
    Terminal_obj;

// The unique terminal pair at which the whole cross cell is observed.
symbol walking_arrow_cross_base
  : τ (Obj (Product_cat (Op_cat Terminal_cat) Terminal_cat))
≔ @Product_pair
    (Op_cat Terminal_cat)
    Terminal_cat
    Terminal_obj
    Terminal_obj;

/*
  Whole generator owner.

  This is the fibre of join_cross_transf at the terminal endpoint pair:

    1 -> Hom_I(0,1).

  The functor, rather than only its object component, is retained so its
  ordinary hom action remains available at the next dimension.
*/
symbol walking_arrow_generator_func
  : τ (Functor
      Terminal_cat
      (Hom_cat
        WalkingArrow_cat
        walking_arrow_src
        walking_arrow_tgt))
≔ @Fibre_func
    (Product_cat (Op_cat Terminal_cat) Terminal_cat)
    (@Terminal_prof Terminal_cat Terminal_cat)
    (@Prof_reindex
      WalkingArrow_cat
      Terminal_cat
      WalkingArrow_cat
      Terminal_cat
      (@Unit_prof WalkingArrow_cat)
      (@join_fst_func Terminal_cat Terminal_cat)
      (@join_snd_func Terminal_cat Terminal_cat))
    (@join_cross_transf Terminal_cat Terminal_cat)
    walking_arrow_cross_base;

// The directed generating arrow 0 -> 1.
symbol walking_arrow_generator
  : τ (Hom WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
≔ @fapp0
    Terminal_cat
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    walking_arrow_generator_func
    Terminal_obj;

// First retained higher action of the whole generator owner.
symbol walking_arrow_generator_next_func
  : τ (Functor
      (Hom_cat Terminal_cat Terminal_obj Terminal_obj)
      (Hom_cat
        (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
        walking_arrow_generator
        walking_arrow_generator))
≔ @fapp1_func
    Terminal_cat
    (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
    walking_arrow_generator_func
    Terminal_obj
    Terminal_obj;
