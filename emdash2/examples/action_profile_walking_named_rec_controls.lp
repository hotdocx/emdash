/* Named recursor computation remains separate from arbitrary functors. */
require open emdash.emdash3_2_walking_end_hit;

assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y)) (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @comp_fapp0 C _ _ _ (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y Z g) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X Y f)
  ≡ (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f));

// Whole-action evaluation first and capped-action evaluation first agree.
assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y)) (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @comp_fapp0 C _ _ _ (@fapp0 (Hom_cat WalkingEnd_cat Y Z) (Hom_cat C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Z)) (@fapp1_func WalkingEnd_cat C (@walking_end_rec_func C x a) Y Z) g) (@fapp0 (Hom_cat WalkingEnd_cat X Y) (Hom_cat C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y)) (@fapp1_func WalkingEnd_cat C (@walking_end_rec_func C x a) X Y) f)
  ≡ (@fapp0 (Hom_cat WalkingEnd_cat X Z) (Hom_cat C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Z)) (@fapp1_func WalkingEnd_cat C (@walking_end_rec_func C x a) X Z) (@comp_fapp0 WalkingEnd_cat X Y Z g f));

assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x))
  (X : τ (Obj WalkingEnd_cat)) ⊢
  @fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X X (@id WalkingEnd_cat X)
  ≡ @id C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X);

type λ C : Cat, λ x : τ (Obj C), λ a : τ (Hom C x x),
  λ X : τ (Obj WalkingEnd_cat), λ Y : τ (Obj WalkingEnd_cat),
  λ f : τ (Hom WalkingEnd_cat X Y), λ g : τ (Hom WalkingEnd_cat X Y),
    @fapp1_func (Hom_cat WalkingEnd_cat X Y)
      (Hom_cat C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y))
      (@fapp1_func WalkingEnd_cat C (@walking_end_rec_func C x a) X Y) f g;

assertnot [C : Cat] (F : τ (Functor WalkingEnd_cat C))
  [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y))
  (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @eq_refl (Hom C (@fapp0 WalkingEnd_cat C F X) (@fapp0 WalkingEnd_cat C F Z))
    (@fapp1_fapp0 WalkingEnd_cat C F X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f))
  : τ (@= (Hom C (@fapp0 WalkingEnd_cat C F X) (@fapp0 WalkingEnd_cat C F Z))
    (@fapp1_fapp0 WalkingEnd_cat C F X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f))
    (@comp_fapp0 C _ _ _ (@fapp1_fapp0 WalkingEnd_cat C F Y Z g)
      (@fapp1_fapp0 WalkingEnd_cat C F X Y f)));

assertnot [C : Cat] (x : τ (Obj C)) (a b : τ (Hom C x x))
  (f g : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢
  @comp_fapp0 C x x x
    (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base g)
    (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x b) walking_base walking_base f)
  ≡ @fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base
      (@comp_fapp0 WalkingEnd_cat walking_base walking_base walking_base g f);
