/* NON-LIBRARY companion: legitimate covariant native Hom action.
   This file deliberately does not import the Empty reproducer. It checks
   direction and retained higher action; it is not a consistency certificate. */
require open emdash.emdash3_2;

symbol homd_target_forward_control [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  : τ (Functor (Hom_cat C u (@fapp0 Z C F x))
      (Hom_cat C u (@fapp0 Z C F y)))
≔ @fapp1_fapp0 Z Cat_cat (@hom_ C Z F u) x y p;

symbol homd_target_forward_application [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  (h : τ (Hom C u (@fapp0 Z C F x)))
  : τ (@= (Hom C u (@fapp0 Z C F y))
      (@fapp0 (Hom_cat C u (@fapp0 Z C F x)) (Hom_cat C u (@fapp0 Z C F y))
        (@homd_target_forward_control Z C F x y u p) h)
      (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
        (@fapp1_fapp0 Z C F x y p) h))
≔ @eq_refl (Hom C u (@fapp0 Z C F y))
    (@comp_fapp0 C u (@fapp0 Z C F x) (@fapp0 Z C F y)
      (@fapp1_fapp0 Z C F x y p) h);

symbol homd_target_forward_identity [C : Cat]
  (x y : τ (Obj C)) (p : τ (Hom C x y))
  : τ (@= (Hom C x y)
      (@fapp0 (Hom_cat C x x) (Hom_cat C x y)
        (@homd_target_forward_control C C (@id_func C) x y x p) (@id C x)) p)
≔ @eq_refl (Hom C x y) p;

assert [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y))
  (a b : τ (Hom C u (@fapp0 Z C F x))) ⊢
  @fapp1_func (Hom_cat C u (@fapp0 Z C F x)) (Hom_cat C u (@fapp0 Z C F y))
    (@homd_target_forward_control Z C F x y u p) a b
  : τ (Functor (Hom_cat (Hom_cat C u (@fapp0 Z C F x)) a b)
      (Hom_cat (Hom_cat C u (@fapp0 Z C F y))
        (@fapp0 (Hom_cat C u (@fapp0 Z C F x)) (Hom_cat C u (@fapp0 Z C F y))
          (@homd_target_forward_control Z C F x y u p) a)
        (@fapp0 (Hom_cat C u (@fapp0 Z C F x)) (Hom_cat C u (@fapp0 Z C F y))
          (@homd_target_forward_control Z C F x y u p) b)));

assertnot [Z C : Cat] (F : τ (Functor Z C))
  (x y : τ (Obj Z)) (u : τ (Obj C)) (p : τ (Hom Z x y)) ⊢
  @homd_target_forward_control Z C F x y u p
  : τ (Functor (Hom_cat C u (@fapp0 Z C F y))
      (Hom_cat C u (@fapp0 Z C F x)));
