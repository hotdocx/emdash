/*
  Reviewer example: the walking arrow as the directed join of two points.

  The endpoint objects and generator are projections of the existing join
  inclusions and internally natural cross cell.  No second interval primitive
  or standalone generating-arrow constant is used.
*/

require open emdash.emdash3_2_walking_arrow;

assert ⊢
  WalkingArrow_cat
  ≡ @Join_cat Terminal_cat Terminal_cat;

assert ⊢
  walking_arrow_src
  : τ (Obj WalkingArrow_cat);

assert ⊢
  walking_arrow_tgt
  : τ (Obj WalkingArrow_cat);

// The two visible join constructors do not collapse.
assertnot ⊢
  walking_arrow_src
  ≡ walking_arrow_tgt;

assert ⊢
  walking_arrow_generator_func
  : τ (Functor
      Terminal_cat
      (Hom_cat
        WalkingArrow_cat
        walking_arrow_src
        walking_arrow_tgt));

assert ⊢
  walking_arrow_generator_func
  ≡ @Fibre_func
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

// The ordinary generator is the terminal component of its whole owner.
assert ⊢
  walking_arrow_generator
  ≡ @fapp0
      Terminal_cat
      (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      walking_arrow_generator_func
      Terminal_obj;

assert ⊢
  walking_arrow_generator
  : τ (Hom WalkingArrow_cat walking_arrow_src walking_arrow_tgt);

// The next hom action remains available; the interface is not capped at the
// generating 1-arrow.
assert ⊢
  walking_arrow_generator_next_func
  : τ (Functor
      (Hom_cat Terminal_cat Terminal_obj Terminal_obj)
      (Hom_cat
        (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
        walking_arrow_generator
        walking_arrow_generator));

assert ⊢
  walking_arrow_generator_next_func
  ≡ @fapp1_func
      Terminal_cat
      (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      walking_arrow_generator_func
      Terminal_obj
      Terminal_obj;

// The curated interval remains directed join, not Cartesian product.
assertnot ⊢
  WalkingArrow_cat
  ≡ @Product_cat Terminal_cat Terminal_cat;
