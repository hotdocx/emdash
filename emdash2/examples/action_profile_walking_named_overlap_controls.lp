/* Owner-position overlap observations: identities, generators and the
   four target-category presentations retain their qualified paths. */
require open emdash.emdash3_2_walking_end_hit;
require open emdash.emdash3_2_gray_profiles;

assert [D : Cat] (x : τ (Obj (Op_cat D))) (a : τ (Hom (Op_cat D) x x))
  [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y)) (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @walking_end_rec_composition_path (Op_cat D) x a X Y Z g f
  : τ (@= (Hom (Op_cat D) (@fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) X) (@fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) Z))
    (@fapp1_fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f))
    (@comp_fapp0 (Op_cat D) (@fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) X) (@fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) Y) (@fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) Z) (@fapp1_fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) Y Z g) (@fapp1_fapp0 WalkingEnd_cat (Op_cat D) (@walking_end_rec_func (Op_cat D) x a) X Y f)));

assert  (x : τ (Obj Terminal_cat)) (a : τ (Hom Terminal_cat x x))
  [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y)) (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @walking_end_rec_composition_path Terminal_cat x a X Y Z g f
  : τ (@= (Hom Terminal_cat (@fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) X) (@fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) Z))
    (@fapp1_fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f))
    (@comp_fapp0 Terminal_cat (@fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) X) (@fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) Y) (@fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) Z) (@fapp1_fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) Y Z g) (@fapp1_fapp0 WalkingEnd_cat Terminal_cat (@walking_end_rec_func Terminal_cat x a) X Y f)));

assert [D : Cat] (x : τ (Obj (EqSkeleton_cat (cat_succ cat_zero) D))) (a : τ (Hom (EqSkeleton_cat (cat_succ cat_zero) D) x x))
  [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y)) (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @walking_end_rec_composition_path (EqSkeleton_cat (cat_succ cat_zero) D) x a X Y Z g f
  : τ (@= (Hom (EqSkeleton_cat (cat_succ cat_zero) D) (@fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) X) (@fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) Z))
    (@fapp1_fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f))
    (@comp_fapp0 (EqSkeleton_cat (cat_succ cat_zero) D) (@fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) X) (@fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) Y) (@fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) Z) (@fapp1_fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) Y Z g) (@fapp1_fapp0 WalkingEnd_cat (EqSkeleton_cat (cat_succ cat_zero) D) (@walking_end_rec_func (EqSkeleton_cat (cat_succ cat_zero) D) x a) X Y f)));

assert [A B : Cat] (x : τ (Obj (@StrictFunctor_cat A B))) (a : τ (Hom (@StrictFunctor_cat A B) x x))
  [X Y Z : τ (Obj WalkingEnd_cat)] (f : τ (Hom WalkingEnd_cat X Y)) (g : τ (Hom WalkingEnd_cat Y Z)) ⊢
  @walking_end_rec_composition_path (@StrictFunctor_cat A B) x a X Y Z g f
  : τ (@= (Hom (@StrictFunctor_cat A B) (@fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) X) (@fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) Z))
    (@fapp1_fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) X Z (@comp_fapp0 WalkingEnd_cat X Y Z g f))
    (@comp_fapp0 (@StrictFunctor_cat A B) (@fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) X) (@fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) Y) (@fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) Z) (@fapp1_fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) Y Z g) (@fapp1_fapp0 WalkingEnd_cat (@StrictFunctor_cat A B) (@walking_end_rec_func (@StrictFunctor_cat A B) x a) X Y f)));

assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢ @walking_end_rec_composition_path C x a walking_base walking_base walking_base walking_loop p
  : τ (@= (Hom C x x) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base (@comp_fapp0 WalkingEnd_cat walking_base walking_base walking_base walking_loop p)) (@comp_fapp0 C x x x (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base walking_loop) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base p)));
assertnot [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢ (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base (@comp_fapp0 WalkingEnd_cat walking_base walking_base walking_base walking_loop p)) ≡ (@comp_fapp0 C x x x (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base walking_loop) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base p));

assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢ @walking_end_rec_composition_path C x a walking_base walking_base walking_base p walking_loop
  : τ (@= (Hom C x x) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base (@comp_fapp0 WalkingEnd_cat walking_base walking_base walking_base p walking_loop)) (@comp_fapp0 C x x x (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base p) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base walking_loop)));
assertnot [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) (p : τ (Hom WalkingEnd_cat walking_base walking_base)) ⊢ (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base (@comp_fapp0 WalkingEnd_cat walking_base walking_base walking_base p walking_loop)) ≡ (@comp_fapp0 C x x x (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base p) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) walking_base walking_base walking_loop));

assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) [X Y : τ (Obj WalkingEnd_cat)] (p : τ (Hom WalkingEnd_cat X Y)) ⊢
  @comp_fapp0 C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y Y (@id WalkingEnd_cat Y)) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X Y p)
  ≡ (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X Y p);

assert [C : Cat] (x : τ (Obj C)) (a : τ (Hom C x x)) [X Y : τ (Obj WalkingEnd_cat)] (p : τ (Hom WalkingEnd_cat X Y)) ⊢
  @comp_fapp0 C (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X) (@fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) Y) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X Y p) (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X X (@id WalkingEnd_cat X))
  ≡ (@fapp1_fapp0 WalkingEnd_cat C (@walking_end_rec_func C x a) X Y p);
