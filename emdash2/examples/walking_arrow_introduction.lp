/* Concrete arrow introduction and its actual whole/point evaluation. */
require open emdash.emdash3_2_walking_arrow_introduction;
require open emdash.emdash3_2_diagram_evaluation;

assert (C : Cat) (x y : τ (Obj C)) (f : τ (Hom C x y))
  ⊢ @fapp0 WalkingArrow_cat C (@walking_arrow_func C x y f) walking_arrow_src ≡ x;

assert (C : Cat) (x y : τ (Obj C)) (f : τ (Hom C x y))
  ⊢ @fapp0 WalkingArrow_cat C (@walking_arrow_func C x y f) walking_arrow_tgt ≡ y;

assert (C : Cat) (x y : τ (Obj C)) (f : τ (Hom C x y))
  ⊢ @fapp1_fapp0 WalkingArrow_cat C (@walking_arrow_func C x y f)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ f;

// Whole generator action before capping; the generic join reviewer also
// exercises its next Hom action.
assert (C : Cat) (x y : τ (Obj C)) (f : τ (Hom C x y))
  ⊢ @comp_cat_fapp0 Terminal_cat
      (Hom_cat WalkingArrow_cat walking_arrow_src walking_arrow_tgt)
      (Hom_cat C x y)
      (@fapp1_func WalkingArrow_cat C (@walking_arrow_func C x y f)
        walking_arrow_src walking_arrow_tgt)
      walking_arrow_generator_func
    ≡ @Obj_func (Hom_cat C x y) f;

// The universal differential from the preceding tranche evaluates to f.
assert (C : Cat) (x y : τ (Obj C)) (f : τ (Hom C x y))
  ⊢ @tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
      (@walking_arrow_func C x y f)
      (@diagram_evaluation_transf WalkingArrow_cat C
        walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    ≡ f;

assertnot (C : Cat) (x y : τ (Obj C)) (f other : τ (Hom C x y))
  ⊢ @fapp1_fapp0 WalkingArrow_cat C (@walking_arrow_func C x y f)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator ≡ other;

assertnot ⊢ @fapp0 WalkingArrow_cat WalkingArrow_cat
    (@walking_arrow_func WalkingArrow_cat walking_arrow_src walking_arrow_tgt
      walking_arrow_generator) walking_arrow_src
  ≡ @fapp0 WalkingArrow_cat WalkingArrow_cat
    (@walking_arrow_func WalkingArrow_cat walking_arrow_src walking_arrow_tgt
      walking_arrow_generator) walking_arrow_tgt;
